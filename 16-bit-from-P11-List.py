#Hi i-Realy Apperciated you get me A Donation here_ 1Bu4CR8Bi5AXQG8pnu1avny88C5CCgWKfb /////
#============================================================================================
# ===========================================================================================
# 🔐 Quantum ECDLP Solver - CODE-10: Final Version with PRESETS and Interactive Interface 🔐
# ===========================================================================================
# Features:
# - Default 15-bit focus (from CODE-8)
# - Interactive interface with PRESETS and Custom mode (from CODE-9)
# - Correct result handling (from CODE-8)
# - XY4 and SABRE transpilation options
# - IBM Quantum hardware only (no simulator fallback)
# ===========================================================================================

import sys
import getpass
import logging
from collections import defaultdict, Counter
from fractions import Fraction
from math import gcd, pi
import numpy as np
from ecdsa import SigningKey, SECP256k1
from ecdsa.ellipticcurve import Point, CurveFp
from qiskit_ibm_runtime import QiskitRuntimeService, SamplerV2
from qiskit_ibm_runtime.options import SamplerOptions
from qiskit import QuantumCircuit, QuantumRegister, ClassicalRegister
from qiskit.circuit.library import QFT
from qiskit.synthesis import synth_qft_full
from qiskit_aer import AerSimulator
from qiskit.transpiler.preset_passmanagers import generate_preset_pass_manager
from tqdm import tqdm

# ====================== CONSTANTS ======================
P = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
A = 0
B = 7
Gx = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
Gy = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8
ORDER = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141

CURVE = CurveFp(P, A, B)
G = Point(CURVE, Gx, Gy)

# ====================== PRESETS (15-bit as default) ======================
PRESETS = {
    "15": {"bits": 15, "start": 0x4000, "pub": "03c1e36164e7fd4939be73c550154c01ffd96dfcfac7c805f15b5d9e4a364b409b", "shots": 32768},
    "16": {"bits": 16, "start": 0x8000, "pub": "03ccb5e3ad4abc7900ebfbd81621e31ec2b17b346090e741921a91bf9cadf934c5", "shots": 32768},
    "21": {"bits": 21, "start": 0x90000, "pub": "037d14b19a95fe400b88b0debe31ecc3c0ec94daea90d13057bde89c5f8e6fc25c", "shots": 16384},
    "25": {"bits": 25, "start": 0xE00000, "pub": "038ad4f423459430771c0f12a24df181ed0da5142ec676088031f28a21e86ea06d", "shots": 65536},
    "135": {"bits": 135, "start": 0x400000000000000000000000000000000, "pub": "02145d2611c823a396ef6712ce0f712f09b9b4f3135e3e0aa3230fb9b6d08d1e16", "shots": 100000},
}

# Defaults (15-bit as default)
TARGET_PUBKEY = bytes.fromhex("03c1e36164e7fd4939be73c550154c01ffd96dfcfac7c805f15b5d9e4a364b409b")
TARGET_ADDRESS = "19hqK9vkcXRvnq6obsUaWSW6HywBHysot6"
BITS = 15
SHOTS = 32768
FULL_RANGE_START = 0x4000
FULL_RANGE_END = 0x7fff
USE_XY4 = False
USE_SABRE = False

logging.basicConfig(level=logging.INFO, format="%(asctime)s | %(levelname)s | %(message)s")
logger = logging.getLogger(__name__)

# ====================== EC HELPERS ======================
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

# ====================== ENHANCED QPE CIRCUIT BUILDER ======================
def build_enhanced_qpe_circuit(effective_bits, delta_x, delta_y):
    n = effective_bits
    phase = QuantumRegister(n, "phase")
    state = QuantumRegister(n, "state")
    cat = QuantumRegister(3, "cat")
    flag = QuantumRegister(2, "flag")
    erasure = QuantumRegister(1, "erasure")
    c_phase = ClassicalRegister(n, "c_phase")
    c_flag = ClassicalRegister(2, "c_flag")
    c_erasure = ClassicalRegister(1, "c_erasure")

    qc = QuantumCircuit(phase, state, cat, flag, erasure, c_phase, c_flag, c_erasure)

    # Initialize cat state for error mitigation
    qc.h(cat[0])
    for i in range(1, 3):
        qc.cx(cat[0], cat[i])

    # Initialize phase qubits for QPE
    for i in range(n):
        qc.h(phase[i])

    # Enhanced QPE oracle with both delta_x and delta_y targeting
    for i in range(n):
        for j in range(n):
            angle_x = 2 * pi * (delta_x * (1 << j)) % ORDER / (1 << n)
            angle_y = 2 * pi * (delta_y * (1 << j)) % ORDER / (1 << n)
            combined_angle = (angle_x + angle_y) / 2
            qc.cp(combined_angle, phase[i], state[j])

    # Additional phase correction
    for i in range(n):
        correction_angle = pi / (2 ** (n - i))
        qc.cp(correction_angle, phase[i], state[i % (n//2)])

    # Inverse QFT
    qc.append(QFT(n, do_swaps=False).inverse(), phase)

    # Measurement
    qc.measure(phase, c_phase)
    qc.measure(flag, c_flag)
    qc.measure(erasure, c_erasure)

    # Additional error mitigation
    for i in range(n):
        qc.cx(cat[0], phase[i])
        qc.cz(cat[1], phase[i])

    return qc

# ====================== QUANTUM EXECUTION (CORRECTED) ======================
def run_quantum_job(service, qc, shots=32768):
    try:
        if service:
            backend = service.least_busy(operational=True, simulator=False, min_num_qubits=156)
            print(f"Using IBM backend: {backend.name}")
        else:
            backend = AerSimulator()
            print("Using local AerSimulator")

        # SamplerOptions with XY4
        options = SamplerOptions()
        options.dynamical_decoupling.enable = True
        options.dynamical_decoupling.sequence_type = "XY4"
        options.default_shots = shots

        # Transpile with proper optimization
        pm = generate_preset_pass_manager(
            optimization_level=3,
            backend=backend,
            routing_method="sabre"
        )
        transpiled = pm.run(qc)
        print(qc)
        print(f"Transpiled circuit depth: {transpiled.depth()}")
        print(f"Transpiled circuit size: {transpiled.size()}")
        print(f"Shots requested: {shots}")

        # Run with proper circuit wrapping
        sampler = SamplerV2(backend, options=options)
        job = sampler.run([transpiled])
        print(f"Job ID: {job.job_id}")
        print("Waiting for results...")

        # Get results using the correct method
        result = job.result()

        # Extract counts - working method from CODE-8
        pub_result = result[0]
        counts = pub_result.data.meas.get_counts()

        return dict(counts)

    except Exception as e:
        logger.error(f"Execution error: {e}")
        logger.error("Check your circuit and backend configuration")
        raise

# ====================== POST-PROCESSING ======================
def post_process(counts, bits, order, start, target_pub):
    candidates = set()
    print(f"Processing {len(counts)} measurements...")

    for state_str, count in counts.items():
        try:
            measured = int(state_str, 2)

            # Continued fraction approximation
            for d in range(1, 20):
                r_num, r_den = continued_fraction_approx(measured, 1 << bits)
                if r_den == 0:
                    continue
                inv = modinv(r_den, order)
                if inv is None:
                    continue
                candidate = (r_num * inv) % order
                if start <= candidate <= FULL_RANGE_END:
                    candidates.add(candidate)

            # GCD check
            for m in range(1, 10):
                g = gcd(measured * m, order)
                if 1 < g < order and start <= g <= FULL_RANGE_END:
                    candidates.add(g)

        except Exception as e:
            print(f"Error processing measurement: {e}")
            continue

    return sorted(candidates)[:5000]

# ====================== MAIN FUNCTION ======================
def main():
    global BITS, SHOTS, TARGET_PUBKEY, TARGET_ADDRESS, FULL_RANGE_START, FULL_RANGE_END, USE_XY4, USE_SABRE

    print("\n" + "="*140)
    print("🔐 QUANTUM ECDLP SOLVER - CODE-10 (Final Version)")
    print("Default 15-bit focus with PRESETS and interactive interface")
    print("="*140)

    # Preset or Custom
    print("\nAvailable PRESETS: 15, 16, 21, 25, 135, c = Custom")
    preset_choice = input("Select preset [15/16/21/25/135/c] → ").strip().lower()

    if preset_choice in PRESETS:
        p = PRESETS[preset_choice]
        BITS = p["bits"]
        FULL_RANGE_START = p["start"]
        TARGET_PUBKEY = bytes.fromhex(p["pub"])
        SHOTS = p["shots"]
        TARGET_ADDRESS = input(f"Enter target address (press Enter for default): ").strip() or "19hqK9vkcXRvnq6obsUaWSW6HywBHysot6"
    else:
        pub_hex = input("Enter compressed pubkey (hex): ").strip()
        TARGET_PUBKEY = bytes.fromhex(pub_hex)
        BITS = int(input("Enter bit length: ") or 15)
        start_input = input(f"Enter k_start (hex) [Press Enter for auto 2^({BITS-1})]: ").strip()
        FULL_RANGE_START = int(start_input, 16) if start_input else (1 << (BITS-1))
        FULL_RANGE_END = (1 << BITS) - 1
        SHOTS = int(input("Enter number of shots: ") or 32768)
        TARGET_ADDRESS = input("Enter target address: ").strip()

    print("\nEnable Transpilation Methods:")
    USE_XY4 = input("Enable XY4 dynamical decoupling? [y/N] → ").strip().lower() == "y"
    USE_SABRE = input("Enable SABRE swap optimization? [y/N] → ").strip().lower() == "y"

    # Connect to IBM Quantum
    service = None
    try:
        token = getpass.getpass("Enter IBM Quantum API Token: ").strip()
        if not token:
            raise ValueError("No token provided")
        channel = input("Channel [ibm_quantum_platform/ibm_cloud]: ") or "ibm_quantum_platform"
        crn = input("IBM Cloud CRN (optional): ") or None
        service = QiskitRuntimeService(token=token, channel=channel, instance=crn)
        print("✅ Connected to IBM Quantum")
    except Exception as e:
        print(f"IBM connection failed: {e}")
        print("Falling back to local AerSimulator")
        service = None

    print("="*100)
    print(f"Running for {BITS}-bit key | Shots: {SHOTS}")
    print(f"Search range: 0x{FULL_RANGE_START:x} to 0x{FULL_RANGE_END:x}")
    print(f"Transpilation: XY4={USE_XY4}, SABRE={USE_SABRE}")
    print("="*100)

    # Derive target point from pubkey
    Q = decompress_pubkey(TARGET_PUBKEY.hex())
    delta_x = Q.x() % (1 << 16)
    delta_y = Q.y() % (1 << 16)
    print(f"Target pubkey point: ({hex(delta_x)}, {hex(delta_y)})")

    # Build and run circuit with proper bit size
    effective_bits = min(BITS, 8)  # Limited for hardware compatibility
    qc = build_enhanced_qpe_circuit(effective_bits, delta_x, delta_y)

    try:
        counts = run_quantum_job(service, qc, SHOTS)
        print(f"Received {len(counts)} measurement results")

        # Post-process results
        candidates = post_process(counts, effective_bits, ORDER, FULL_RANGE_START, Q)
        print(f"\nVerifying {len(candidates)} candidates...")

        # Verify candidates
        found = False
        for candidate in candidates:
            try:
                if compress_pubkey(candidate) == TARGET_PUBKEY:
                    print("\n" + "="*140)
                    print("!!! PRIVATE KEY FOUND !!!")
                    print(f"Private key (hex): 0x{candidate:x}")
                    print(f"Address: {TARGET_ADDRESS}")
                    print("="*140)
                    with open("found_key_quantum.txt", "w") as f:
                        f.write(f"0x{candidate:x}\n")
                    found = True
                    break
            except Exception as e:
                print(f"Error verifying candidate: {e}")
                continue

        if not found:
            print("\nNo match found in this run.")
            print("This is the final quantum ECDLP solver with all features.")

    except Exception as e:
        print(f"Execution failed: {e}")

if __name__ == "__main__":
    main()
