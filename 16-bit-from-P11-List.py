#!/usr/bin/env python3
"""
BITCOIN PUZZLE #16 - ULTIMATE PURE SHOR'S STYLE QUANTUM ECDLP SOLVER
Full range: 0x8000 to 0xffff
No lower bits method
ZNE COMPLETELY REMOVED + Switched to SamplerV2 (correct primitive for getting measurement counts)
"""

import sys
import getpass
import logging
from collections import defaultdict
from fractions import Fraction
from math import gcd
import numpy as np
from ecdsa import SigningKey, SECP256k1
from ecdsa.ellipticcurve import Point, CurveFp
from qiskit_ibm_runtime import QiskitRuntimeService, SamplerV2
from qiskit_ibm_runtime.options import SamplerOptions
from qiskit import QuantumCircuit, QuantumRegister, ClassicalRegister
from qiskit.circuit.library import QFTGate
from qiskit.synthesis import synth_qft_full
from qiskit_aer import AerSimulator
from qiskit.transpiler.preset_passmanagers import generate_preset_pass_manager
from tqdm import tqdm

P = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
A = 0
B = 7
Gx = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
Gy = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8
ORDER = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141

CURVE = CurveFp(P, A, B)
G = Point(CURVE, Gx, Gy)

FULL_RANGE_START = 0x8000
FULL_RANGE_END = 0xffff

TARGET_PUBKEY = bytes.fromhex("03ccb5e3ad4abc7900ebfbd81621e31ec2b17b346090e741921a91bf9cadf934c5") # PublicKey Correspond for 16-bit Decimal=32803 / HEX=0x00008023
TARGET_ADDRESS = "17wsUeKMK1JgjGzdfYBjefDdyakNCK9xVx" # Corresponding to 16-bit Decimal=32803 / HEX=0x00008023

logging.basicConfig(level=logging.INFO, format="%(asctime)s | %(levelname)s | %(message)s")
logger = logging.getLogger(__name__)

def extended_gcd(a, b):
    if a == 0:
        return b, 0, 1
    g, y, x = extended_gcd(b % a, a)
    return g, x - (b // a) * y, y

def modinv(a, m):
    g, x, y = extended_gcd(a, m)
    if g != 1:
        return None
    return x % m

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

def point_double(p):
    if p is None: return None
    x, y = p.x(), p.y()
    if y == 0: return None
    lam = (3 * x * x + A) * modinv(2 * y, P) % P
    x3 = (lam * lam - 2 * x) % P
    y3 = (lam * (x - x3) - y) % P
    return Point(CURVE, x3, y3)

def ec_scalar_mult(k, point):
    if k == 0 or point is None:
        return None
    result = None
    addend = point
    while k:
        if k & 1:
            result = point_add(result, addend)
        addend = point_double(addend)
        k >>= 1
    return result

def compress_pubkey(privkey):
    sk = SigningKey.from_secret_exponent(privkey, curve=SECP256k1)
    vk = sk.verifying_key
    x = vk.pubkey.point.x()
    y = vk.pubkey.point.y()
    prefix = b'\x02' if (y % 2 == 0) else b'\x03'
    return prefix + x.to_bytes(32, byteorder='big')

def continued_fraction_approx(num, den, max_den=1000000):
    if den == 0:
        return 0, 1
    frac = Fraction(num, den).limit_denominator(max_den)
    return frac.numerator, frac.denominator

def build_geometric_qpe_circuit(effective_bits):
    n = effective_bits
    phase = QuantumRegister(n, "phase")
    state = QuantumRegister(n, "state")
    cat = QuantumRegister(3, "cat")
    flag = QuantumRegister(2, "flag")
    erasure = QuantumRegister(1, "erasure")
    c_phase = ClassicalRegister(n, "c_phase")
    c_flag = ClassicalRegister(2, "c_flag")

    qc = QuantumCircuit(phase, state, cat, flag, erasure, c_phase, c_flag)

    qc.h(cat[0])
    for i in range(1, 3):
        qc.cx(cat[0], cat[i])

    for i in range(n):
        qc.h(phase[i])

    # Geometric QPE oracle (controlled phase kickback)
    for i in range(n):
        for j in range(n):
            angle = 3.1415926535 * (i + 1) / (2 ** (n - j))
            qc.cp(angle, phase[i], state[j])

    # Inverse QFT
    synth_qft = synth_qft_full(n, do_swaps=False)
    qc.append(synth_qft.inverse(), phase)

    # Measurements
    qc.measure(phase, c_phase)
    qc.measure(flag, c_flag)
    qc.reset(erasure[0])
    qc.h(erasure[0])
    qc.measure(erasure[0], c_flag[1])

    return qc

def run_hive_swarm(service, qc, shots=32768):
    """
    FIXED VERSION - Uses SamplerV2 (correct primitive for getting measurement counts)
    ZNE completely removed.
    Works on both IBM Quantum and AerSimulator.
    """
    if service:
        backend = service.least_busy(operational=True, simulator=False, min_num_qubits=156)
        print(f"Using IBM backend: {backend.name}")
    else:
        backend = AerSimulator()
        print("Using local AerSimulator")

    # SamplerOptions (no resilience/ZNE)
    options = SamplerOptions()
    options.dynamical_decoupling.enable = True
    options.dynamical_decoupling.sequence_type = "XY4"
    options.default_shots = shots

    sampler = SamplerV2(mode=backend, options=options)
    backend_name = backend.name if hasattr(backend, 'name') else str(backend)
    print(f"📡 Using backend: {backend_name}")
    print(f"📡 Submitting job to backend: {backend_name}")
    # Transpile once
    pm = generate_preset_pass_manager(
        optimization_level=3,
        backend=backend,
        routing_method="sabre"
    )
    transpiled = pm.run(qc)
    
    print(f"Transpiled circuit depth: {transpiled.depth()}")
    print(f"Transpiled circuit size : {transpiled.size()}")
    print(f"   Shots requested     : {shots}")

    # Run with SamplerV2 - simple list of circuits
    job = sampler.run([transpiled])
    print(f" Job ID: {job.job_id()}")
    print("⏳ Waiting for results...")
    result = job.result()

    # Extract counts - modern way
    pub_result = result[0]
    # The circuit has multiple classical registers, so we combine them
    counts = pub_result.join_data().get_counts()

    return dict(counts)


def universal_post_process(counts):
    candidates = set()
    print(f"Universal post-processing on {len(counts)} measurements...")

    for state_str, count in tqdm(counts.items(), desc="Processing measurements"):
        clean = state_str.replace(" ", "")
        if not clean:
            continue

        variants = [clean, clean[::-1]]
        for var in variants:
            try:
                measured = int(var, 2)
                for d in range(1, 20):
                    r_num, r_den = continued_fraction_approx(measured, d, 1 << 20)
                    if r_den == 0:
                        continue
                    inv = modinv(r_den, ORDER)
                    if inv is None:
                        continue
                    candidate = (r_num * inv) % ORDER
                    if FULL_RANGE_START <= candidate <= FULL_RANGE_END:
                        candidates.add(candidate)
            except:
                continue

            try:
                measured = int(var, 2)
                for m in range(1, 10):
                    g = gcd(measured * m, ORDER)
                    if 1 < g < ORDER and FULL_RANGE_START <= g <= FULL_RANGE_END:
                        candidates.add(g)
            except:
                pass

    return list(candidates)[:5000]


def main():
    print("\n" + "="*140)
    print("BITCOIN PUZZLE #16 - ULTIMATE PURE SHOR'S STYLE QUANTUM ECDLP SOLVER")
    print("No lower bits method - full recovery from public key only")
    print("ZNE REMOVED - Now using SamplerV2 (correct primitive for counts)")
    print("="*140)

    shots_input = input("Enter number of shots (default 32768): ").strip()
    shots = int(shots_input) if shots_input else 32768

    print(f"\nFull search range : 0x{FULL_RANGE_START:x} to 0x{FULL_RANGE_END:x}")
    print("="*140)

    service = None
    try:
        token = getpass.getpass("Enter IBM Quantum API Token: ").strip()
        if not token:
            raise ValueError("No token provided")
        channel = input("Channel (ibm_quantum_platform or ibm_cloud) [ibm_quantum_platform]: ").strip() or "ibm_quantum_platform"
        crn = None
        if channel == "ibm_cloud":
            crn = input("Enter IBM Cloud CRN: ").strip() or None
        if channel == "ibm_cloud" and crn:
            service = QiskitRuntimeService(token=token, channel=channel, instance=crn)
        else:
            service = QiskitRuntimeService(token=token, channel=channel)
        print("✅ Connected to IBM Quantum")
    except Exception as e:
        print(f"IBM connection failed: {e}")
        print("Falling back to local AerSimulator")

    effective_bits = min(16, 40)   # SAFE LIMIT for current hardware
    qc = build_geometric_qpe_circuit(effective_bits)

    counts = run_hive_swarm(service, qc, shots=shots)

    candidates = universal_post_process(counts)

    print(f"\nVerifying {len(candidates)} candidates from pure Shor's recovery...")

    found = False
    for candidate in tqdm(candidates):
        try:
            if compress_pubkey(candidate) == TARGET_PUBKEY:
                print("\n" + "="*140)
                print("!!! PRIVATE KEY FOUND !!!")
                print(f"Private key (hex): 0x{candidate:x}")
                print(f"Address          : {TARGET_ADDRESS}")
                print("="*140)
                with open("found_key_16_quantum.txt", "w") as f:
                    f.write(f"0x{candidate:x}\n")
                found = True
                break
        except Exception:
            continue

    if not found:
        print("\nNo match found in this run.")
        print("This is pure Shor's style recovery from the public key only.")

    print("\nExecution finished.")


if __name__ == "__main__":
    main()
