#!/usr/bin/env python3
# ===========================================================================================
# 🔐 Quantum ECDLP Solver with IPE, XY4, SABRE (IBM HARDWARE ONLY) 🔐
# ===========================================================================================
# Features:
# - Runs ONLY on real IBM Quantum hardware (NO SIMULATOR)
# - XY4 and SABRE transpilation (as in reference code)
# - PRESETS for common bit lengths and targets
# - Custom mode for arbitrary parameters
# - Interactive input for target pubkey, bits, shots, and hardware selection
# - IBM Quantum API token and CRN instance REQUIRED
# ===========================================================================================

import logging
import math
import os
import time
import numpy as np
from collections import defaultdict, Counter
from fractions import Fraction
from math import gcd, pi
from qiskit import QuantumCircuit, QuantumRegister, ClassicalRegister, transpile
from qiskit.circuit.library import QFTGate
from qiskit.synthesis import synth_qft_full
from qiskit_ibm_runtime import QiskitRuntimeService, SamplerV2, Options
from qiskit_ibm_runtime.options import SamplerOptions
from qiskit.transpiler.preset_passmanagers import generate_preset_pass_manager
from ecdsa.ellipticcurve import Point, CurveFp
from ecdsa import SigningKey, SECP256k1

# ====================== CONSTANTS ======================
P = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
A, B = 0, 7
Gx = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
Gy = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8
N = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
CURVE = CurveFp(P, A, B)
G = Point(CURVE, Gx, Gy)

# ====================== PRESETS ======================
PRESETS = {
    "21": {"bits": 21, "start": 0x90000, "pub": "037d14b19a95fe400b88b0debe31ecc3c0ec94daea90d13057bde89c5f8e6fc25c", "shots": 16384},
    "25": {"bits": 25, "start": 0xE00000, "pub": "038ad4f423459430771c0f12a24df181ed0da5142ec676088031f28a21e86ea06d", "shots": 65536},
    "135": {"bits": 135, "start": 0x400000000000000000000000000000000, "pub": "02145d2611c823a396ef6712ce0f712f09b9b4f3135e3e0aa3230fb9b6d08d1e16", "shots": 100000},
}

# Defaults (can be overridden by user input)
TARGET_PUBKEY = bytes.fromhex("03ccb5e3ad4abc7900ebfbd81621e31ec2b17b346090e741921a91bf9cadf934c5") # PublicKey Correspond for 16-bit Decimal=32803 / HEX=0x00008023
TARGET_ADDRESS = "17wsUeKMK1JgjGzdfYBjefDdyakNCK9xVx" # Corresponding to 16-bit Decimal=32803 / HEX=0x00008023
BITS = 16
SHOTS = 32768
FULL_RANGE_START = 0x8000
FULL_RANGE_END = 0xffff
USE_XY4 = False
USE_SABRE = False

logging.basicConfig(level=logging.INFO, format="%(asctime)s | %(levelname)s | %(message)s")
logger = logging.getLogger(__name__)

# ====================== EC HELPERS ======================
def modinv(a, m):
    g, x, y = math.gcd(a, m), 0, 1
    if g != 1:
        return None
    m0, x0, y0 = m, 0, 1
    while a != 0:
        q = m // a
        m, a = a, m % a
        x0, x = x - q * x0, x0
        y0, y = y - q * y0, y0
    return x0 % m0

def decompress_pubkey(hex_key):
    prefix = int(hex_key[:2], 16)
    x = int(hex_key[2:], 16)
    y_sq = (pow(x, 3, P) + B) % P
    y = pow(y_sq, (P + 1) // 4, P)
    if (y % 2) != (prefix % 2):
        y = P - y
    return Point(CURVE, x, y)

def point_add(p1, p2):
    if p1 is None: return p2
    if p2 is None: return p1
    x1, y1 = p1.x(), p1.y()
    x2, y2 = p2.x(), p2.y()
    if x1 == x2 and (y1 + y2) % P == 0: return None
    if x1 == x2 and y1 == y2:
        lam = (3 * x1 * x1 + A) * modinv(2 * y1, P) % P
    else:
        lam = (y2 - y1) * modinv(x2 - x1, P) % P
    x3 = (lam * lam - x1 - x2) % P
    y3 = (lam * (x1 - x3) - y1) % P
    return Point(CURVE, x3, y3)

def ec_scalar_mult(k, point):
    result = None
    addend = point
    while k:
        if k & 1:
            result = point_add(result, addend)
        addend = point_add(addend, addend)
        k >>= 1
    return result

def compress_pubkey(privkey):
    sk = SigningKey.from_secret_exponent(privkey, curve=SECP256k1)
    vk = sk.verifying_key
    x = vk.pubkey.point.x()
    y = vk.pubkey.point.y()
    prefix = b'\x02' if (y % 2 == 0) else b'\x03'
    return prefix + x.to_bytes(32, byteorder='big')

# ====================== IPE CIRCUIT BUILDER (Semiclassical) ======================
def build_ipe_circuit(bits):
    ctrl = QuantumRegister(1, "ctrl")
    state = QuantumRegister(bits, "state")
    creg = ClassicalRegister(bits, "meas")
    qc = QuantumCircuit(ctrl, state, creg)

    for k in range(bits):
        if k > 0:
            qc.reset(ctrl[0])
        qc.h(ctrl[0])

        # Semiclassical feedback from previous measurements
        for m in range(k):
            with qc.if_test((creg[m], 1)):
                qc.p(-pi / (2 ** (k - m)), ctrl[0])

        # Oracle: controlled addition of (delta * 2^k) mod N
        angle = (delta.x() * (1 << k)) % N
        for i in range(bits):
            qc.cp(2 * pi * angle / (2 ** (bits - i)), ctrl[0], state[i])

        qc.h(ctrl[0])
        qc.measure(ctrl[0], creg[k])

    return qc

# ====================== EXECUTION (IBM HARDWARE ONLY) ======================
def run_circuit(qc, shots, api_token, crn=None, use_xy4=False, use_sabre=False):
    try:
        QiskitRuntimeService.save_account(channel="ibm_quantum_platform", token=api_token, overwrite=True)
        service = QiskitRuntimeService(instance=crn) if crn else QiskitRuntimeService()
        backend = service.least_busy(operational=True, simulator=False, min_num_qubits=156)
        logger.info(f"Using IBM backend: {backend.name}")

        # SamplerOptions (XY4 enabled via options)
        options = SamplerOptions()
        options.dynamical_decoupling.enable = use_xy4
        options.dynamical_decoupling.sequence_type = "XY4"

        # Transpile with SABRE routing
        pm = generate_preset_pass_manager(
            optimization_level=3,
            backend=backend,
            routing_method="sabre" if use_sabre else None
        )
        transpiled = pm.run(qc)

        logger.info(f"Transpiled circuit depth: {transpiled.depth()}")
        logger.info(f"Transpiled circuit size : {transpiled.size()}")

        sampler = SamplerV2(mode=backend, options=options)
        job = sampler.run([transpiled], shots=shots)
        logger.info(f"Job ID: {job.job_id()}")
        logger.info("Waiting for results...")
        result = job.result()
        return result[0].data.c.get_counts()
    except Exception as e:
        logger.error(f"IBM backend error: {e}")
        logger.error("This code only runs on real IBM hardware. Exiting.")
        exit(1)

# ====================== POST-PROCESSING ======================
def continued_fraction_approx(num, den, max_den=1000000):
    frac = Fraction(num, den).limit_denominator(max_den)
    return frac.numerator, frac.denominator

def post_process(counts, bits, order, start, target_pub):
    qx = target_pub.x()
    for m, cnt in sorted(counts.items(), key=lambda x: x[1], reverse=True)[:200]:
        m = m.replace(" ", "")
        measurements = [int(bit) for bit in m if bit in '01']
        if len(measurements) < bits:
            continue
        phi = sum(b * (1 / 2**(i+1)) for i, b in enumerate(measurements[::-1]))
        num, den = continued_fraction_approx(int(phi * 2**bits), 2**bits, order)
        if den == 0 or gcd(den, order) != 1:
            continue
        k = (num * modinv(den, order)) % order
        candidate = (start + k) % order
        if FULL_RANGE_START <= candidate <= FULL_RANGE_END:
            cp = ec_scalar_mult(candidate, G)
            if cp.x() == qx:
                return candidate
    return None

# ====================== MAIN ======================
def main():
    global delta, BITS, SHOTS, TARGET_PUBKEY, TARGET_ADDRESS, USE_XY4, USE_SABRE

    print("="*100)
    print("🔐 Quantum ECDLP Solver with IPE, XY4, SABRE (IBM HARDWARE ONLY) 🔐")
    print("="*100)

    # Preset or Custom
    print("\nAvailable PRESETS: 21, 25, 135, c = Custom")
    preset_choice = input("Select preset [21/25/135/c] → ").strip().lower()
    if preset_choice in PRESETS:
        p = PRESETS[preset_choice]
        BITS = p["bits"]
        FULL_RANGE_START = p["start"]
        TARGET_PUBKEY = bytes.fromhex(p["pub"])
        SHOTS = p["shots"]
    else:
        pub_hex = input("Enter compressed pubkey (hex): ").strip()
        TARGET_PUBKEY = bytes.fromhex(pub_hex)
        BITS = int(input("Enter bit length: ") or 256)
        start_input = input(f"Enter k_start (hex) [Press Enter for auto 2^({BITS-1})]: ").strip()
        FULL_RANGE_START = int(start_input, 16) if start_input else (1 << (BITS-1))
        SHOTS = int(input("Enter number of shots: ") or 1024)

    address = input(f"Enter target address (press Enter for {TARGET_ADDRESS}): ").strip()
    if address:
        TARGET_ADDRESS = address

    print("\nEnable Transpilation Methods:")
    USE_XY4 = input("Enable XY4 dynamical decoupling? [y/N] → ").strip().lower() == "y"
    USE_SABRE = input("Enable SABRE swap optimization? [y/N] → ").strip().lower() == "y"

    api_token = input("IBM Quantum API token (REQUIRED): ").strip()
    crn = input("IBM Cloud CRN (Enter to skip): ").strip() or None

    print("="*100)
    print(f"Running for {BITS}-bit key | Shots: {SHOTS}")
    print(f"Transpilation: XY4={USE_XY4}, SABRE={USE_SABRE}")
    print("="*100)

    print("Deriving public point Q from TARGET_PUBKEY...")
    Q_real = decompress_pubkey(TARGET_PUBKEY.hex())
    print("✅ Public point Q derived (real secp256k1).")
    delta = Q_real

    qc = build_ipe_circuit(BITS)
    counts = run_circuit(qc, SHOTS, api_token, crn, USE_XY4, USE_SABRE)

    print(f"\nPost-processing {len(counts)} measurement outcomes...")
    found_key = post_process(counts, BITS, N, FULL_RANGE_START, Q_real)

    if found_key:
        print("\n" + "="*80)
        print("!!! PRIVATE KEY FOUND BY QUANTUM IPE !!!")
        print(f"Private key (hex): 0x{found_key:x}")
        print(f"Address: {TARGET_ADDRESS}")
        print("="*80)
        with open("P11_16_bit_quantum_key.txt", "w") as f:
            f.write(f"0x{found_key:x}\n")
    else:
        print("\nNo key recovered in this run. Increase shots or run again.")

if __name__ == "__main__":
    main()
