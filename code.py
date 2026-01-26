import hashlib
import os
import random
import time
from typing import List, Tuple

# ============================================================
# Helpers (Hash, XOR, bit/nibble conversions)
# ============================================================

def H(data: bytes) -> bytes:
    return hashlib.sha256(data).digest()

def FirstBits(data: bytes, nbits: int) -> bytes:
    nbytes = (nbits + 7) // 8
    return data[:nbytes]

def BitsToInt(data: bytes) -> int:
    return int.from_bytes(data, byteorder="big", signed=False)

def XOR(a: bytes, b: bytes) -> bytes:
    return bytes(x ^ y for x, y in zip(a, b))

def split_nibbles(block16: bytes) -> List[int]:
    nibbles = []
    for byte in block16:
        nibbles.append((byte >> 4) & 0xF)
        nibbles.append(byte & 0xF)
    return nibbles

def join_nibbles(nibbles: List[int]) -> bytes:
    out = bytearray(16)
    for i in range(16):
        hi = nibbles[2*i] & 0xF
        lo = nibbles[2*i + 1] & 0xF
        out[i] = (hi << 4) | lo
    return bytes(out)

def bytes_to_bits(block16: bytes) -> List[int]:
    bits = []
    for byte in block16:
        for k in range(7, -1, -1):
            bits.append((byte >> k) & 1)
    return bits

def bits_to_bytes(bits: List[int]) -> bytes:
    out = bytearray(16)
    for i in range(16):
        v = 0
        for k in range(8):
            v = (v << 1) | (bits[i*8 + k] & 1)
        out[i] = v
    return bytes(out)

def hamming_distance(a: bytes, b: bytes) -> int:
    return sum((x ^ y).bit_count() for x, y in zip(a, b))

# ============================================================
# SBOX and inverse SBOX (4-bit)
# ============================================================

SBOX = [0x6, 0x4, 0xC, 0x5,
        0x0, 0x7, 0x2, 0xE,
        0x1, 0xF, 0x3, 0xD,
        0x8, 0xA, 0x9, 0xB]

INV_SBOX = [0] * 16
for i, v in enumerate(SBOX):
    INV_SBOX[v] = i

# ============================================================
# Chess move tables (fixed: different sets)
# ============================================================

MOVE_K32 = [
    (+3, +2), (+3, -2), (-3, +2), (-3, -2),
    (+2, +3), (+2, -3), (-2, +3), (-2, -3),
]

MOVE_B2 = [
    (+2, +2), (+2, -2), (-2, +2), (-2, -2),
]

def BuildMoveTable(deltas: List[Tuple[int, int]]) -> List[List[int]]:
    table = [[] for _ in range(64)]
    for sq in range(64):
        r, c = divmod(sq, 8)
        for dr, dc in deltas:
            nr, nc = r + dr, c + dc
            if 0 <= nr < 8 and 0 <= nc < 8:
                table[sq].append(nr * 8 + nc)
    return table

TABLE_K32 = BuildMoveTable(MOVE_K32)
TABLE_B2  = BuildMoveTable(MOVE_B2)

def GetMoves(step_j: int, current_sq: int, mode: int) -> List[int]:
    if mode == 0:
        return TABLE_K32[current_sq] if (step_j % 2 == 1) else TABLE_B2[current_sq]
    else:
        return TABLE_K32[current_sq] if (step_j % 2 == 0) else TABLE_B2[current_sq]

# ============================================================
# 128-bit permutations
# perm[out_i] = in_i mapping
# ============================================================

def generate_permutations(num: int = 256, seed: bytes = b"PERMUTATIONS_SEED") -> List[List[int]]:
    perms = []
    base = list(range(128))
    for i in range(num):
        rnd = random.Random(BitsToInt(H(seed + i.to_bytes(4, "big"))))
        p = base[:]
        rnd.shuffle(p)
        perms.append(p)
    return perms

PERMUTATIONS = generate_permutations(num=256)

def ApplyPerm(perm: List[int], state16: bytes) -> bytes:
    bits = bytes_to_bits(state16)
    out_bits = [0] * 128
    for out_i in range(128):
        out_bits[out_i] = bits[perm[out_i]]
    return bits_to_bytes(out_bits)

def InversePerm(perm: List[int]) -> List[int]:
    inv = [0] * 128
    for out_i, in_i in enumerate(perm):
        inv[in_i] = out_i
    return inv

# ============================================================
# Key schedule init()
# ============================================================

def init(K: bytes, N: bytes, R: int, W: int):
    seed = H(K + N)
    start_sq = BitsToInt(seed) % 64
    T = FirstBits(seed, 128)

    ROUND_KEY  = [None] * (R + 1)
    ROUND_PERM = [None] * (R + 1)

    mode = 0

    for r in range(1, R + 1):
        if r % 3 == 0:
            mode ^= 1

        current_sq = start_sq
        walk_bytes = bytearray()

        for j in range(1, W + 1):
            h = H(K + N + r.to_bytes(4, "big") + j.to_bytes(4, "big") + T)

            moves = GetMoves(j, current_sq, mode)
            if not moves:
                moves = list(set(TABLE_K32[current_sq] + TABLE_B2[current_sq]))

            idx = BitsToInt(h) % len(moves)
            next_sq = moves[idx]

            delta = current_sq ^ next_sq
            walk_bytes.append(delta & 0xFF)
            current_sq = next_sq

        round_hash = H(K + N + r.to_bytes(4, "big") + bytes(walk_bytes))
        ROUND_KEY[r] = FirstBits(round_hash, 128)

        p_idx = BitsToInt(round_hash) % len(PERMUTATIONS)
        ROUND_PERM[r] = PERMUTATIONS[p_idx]

    return T, ROUND_KEY, ROUND_PERM

def init_frozen(K: bytes, N: bytes, R: int, W: int):
    return init(K, N, R, W)

# ============================================================
# SPN Encrypt / Decrypt
# ============================================================

def Encrypt(P: bytes, K: bytes, N: bytes, R: int = 20, W: int = 32) -> bytes:
    assert len(P) == 16
    T, ROUND_KEY, ROUND_PERM = init(K, N, R, W)

    STATE = XOR(XOR(P, ROUND_KEY[1]), T)

    for r in range(1, R + 1):
        STATE = XOR(STATE, ROUND_KEY[r])
        STATE = join_nibbles([SBOX[x] for x in split_nibbles(STATE)])
        STATE = ApplyPerm(ROUND_PERM[r], STATE)

    return XOR(XOR(STATE, ROUND_KEY[R]), T)

def Decrypt(C: bytes, K: bytes, N: bytes, R: int = 20, W: int = 32) -> bytes:
    assert len(C) == 16
    T, ROUND_KEY, ROUND_PERM = init(K, N, R, W)

    STATE = XOR(XOR(C, T), ROUND_KEY[R])

    for r in range(R, 0, -1):
        STATE = ApplyPerm(InversePerm(ROUND_PERM[r]), STATE)
        STATE = join_nibbles([INV_SBOX[x] for x in split_nibbles(STATE)])
        STATE = XOR(STATE, ROUND_KEY[r])

    return XOR(XOR(STATE, T), ROUND_KEY[1])

# ============================================================
# Frozen rounds (metrics)
# ============================================================

def EncryptKRoundsFrozen(P: bytes, T: bytes, ROUND_KEY: List[bytes], ROUND_PERM: List[List[int]], k: int) -> bytes:
    STATE = XOR(XOR(P, ROUND_KEY[1]), T)
    for r in range(1, k + 1):
        STATE = XOR(STATE, ROUND_KEY[r])
        STATE = join_nibbles([SBOX[x] for x in split_nibbles(STATE)])
        STATE = ApplyPerm(ROUND_PERM[r], STATE)
    return STATE

def flip_bit(block16: bytes, bitpos: int) -> bytes:
    b = bytearray(block16)
    byte_i = bitpos // 8
    bit_i  = 7 - (bitpos % 8)
    b[byte_i] ^= (1 << bit_i)
    return bytes(b)

# ============================================================
# Avalanche Tests
# ============================================================

def AvalanchePerRound_PureSPN(R: int = 20, trials: int = 200, W: int = 32):
    K = os.urandom(16)
    N = os.urandom(16)
    T, ROUND_KEY, ROUND_PERM = init_frozen(K, N, R, W)

    print("\nAvalanche Test (PURE SPN diffusion, frozen init):")
    for k in range(1, R + 1):
        total = 0
        for _ in range(trials):
            P = os.urandom(16)
            C1 = EncryptKRoundsFrozen(P, T, ROUND_KEY, ROUND_PERM, k)
            P2 = flip_bit(P, random.randrange(128))
            C2 = EncryptKRoundsFrozen(P2, T, ROUND_KEY, ROUND_PERM, k)
            total += hamming_distance(C1, C2)

        print(f"Round {k:2d}: avg flipped bits = {total/trials:.2f} / 128")

# ============================================================
# BIC Test (lightweight)
# ============================================================

def compute_correlation(bits1: List[int], bits2: List[int]) -> float:
    n = len(bits1)
    mean1 = sum(bits1) / n
    mean2 = sum(bits2) / n
    num = sum((bits1[i] - mean1) * (bits2[i] - mean2) for i in range(n))
    den1 = sum((bits1[i] - mean1) ** 2 for i in range(n))
    den2 = sum((bits2[i] - mean2) ** 2 for i in range(n))
    denom = (den1 * den2) ** 0.5
    if denom == 0:
        return 0.0
    return num / denom

def measure_bic(P: bytes, T: bytes, ROUND_KEY: List[bytes], ROUND_PERM: List[List[int]], R: int,
                trials: int = 40, bits_to_flip: int = 32):
    bit_positions = random.sample(range(128), bits_to_flip)

    total_corr = 0.0
    total_pairs = 0
    max_corr = 0.0

    for _ in range(trials):
        C1 = EncryptKRoundsFrozen(P, T, ROUND_KEY, ROUND_PERM, R)
        bits1 = bytes_to_bits(C1)

        for bpos in bit_positions:
            P2 = flip_bit(P, bpos)
            C2 = EncryptKRoundsFrozen(P2, T, ROUND_KEY, ROUND_PERM, R)
            bits2 = bytes_to_bits(C2)

            corr = abs(compute_correlation(bits1, bits2))
            total_corr += corr
            max_corr = max(max_corr, corr)
            total_pairs += 1

    print(f"\nBIC Results (abs correlation): mean = {total_corr/total_pairs:.4f}, max = {max_corr:.4f}")

# ============================================================
# Correctness + Performance Benchmark (frozen init)
# ============================================================

def correctness_test(R: int = 20, W: int = 32, tests: int = 200):
    K = os.urandom(16)
    N = os.urandom(16)
    passed = 0

    for _ in range(tests):
        P = os.urandom(16)
        C = Encrypt(P, K, N, R=R, W=W)
        P2 = Decrypt(C, K, N, R=R, W=W)
        if P2 == P:
            passed += 1

    print("\nCorrectness Test")
    print(f"Total tests : {tests}")
    print(f"Passed      : {passed}")
    print(f"Accuracy    : {passed/tests*100:.2f}%")

def perf_benchmark(R: int = 20, W: int = 32, trials: int = 2000):
    K = os.urandom(16)
    N = os.urandom(16)
    T, ROUND_KEY, ROUND_PERM = init_frozen(K, N, R, W)

    def encrypt_frozen(P: bytes) -> bytes:
        STATE = XOR(XOR(P, ROUND_KEY[1]), T)
        for r in range(1, R + 1):
            STATE = XOR(STATE, ROUND_KEY[r])
            STATE = join_nibbles([SBOX[x] for x in split_nibbles(STATE)])
            STATE = ApplyPerm(ROUND_PERM[r], STATE)
        return XOR(XOR(STATE, ROUND_KEY[R]), T)

    def decrypt_frozen(C: bytes) -> bytes:
        STATE = XOR(XOR(C, T), ROUND_KEY[R])
        for r in range(R, 0, -1):
            STATE = ApplyPerm(InversePerm(ROUND_PERM[r]), STATE)
            STATE = join_nibbles([INV_SBOX[x] for x in split_nibbles(STATE)])
            STATE = XOR(STATE, ROUND_KEY[r])
        return XOR(XOR(STATE, T), ROUND_KEY[1])

    t0 = time.perf_counter()
    for _ in range(trials):
        P = os.urandom(16)
        _ = encrypt_frozen(P)
    t1 = time.perf_counter()

    C = encrypt_frozen(os.urandom(16))
    t2 = time.perf_counter()
    for _ in range(trials):
        _ = decrypt_frozen(C)
    t3 = time.perf_counter()

    enc_time = (t1 - t0) / trials
    dec_time = (t3 - t2) / trials

    print("\nPerformance Metrics (per 16-byte block, frozen init)")
    print(f"Rounds (R)           : {R}")
    print(f"Walk length (W)      : {W}")
    print(f"Trials               : {trials}")
    print(f"Avg Encrypt Time     : {enc_time*1000:.6f} ms/block")
    print(f"Avg Decrypt Time     : {dec_time*1000:.6f} ms/block")
    print(f"Enc Throughput       : {(16/enc_time)/(1024*1024):.6f} MB/s")
    print(f"Dec Throughput       : {(16/dec_time)/(1024*1024):.6f} MB/s")

# ============================================================
# Demo
# ============================================================

if __name__ == "__main__":
    R = 20
    W = 32

    K = b"THIS_IS_16_BYTEK"
    N = b"THIS_IS_16_BYTEN"
    P = b"percysbestbuddyi"

    print("Plaintext :", P)
    C = Encrypt(P, K, N, R=R, W=W)
    print("Ciphertext:", C.hex())
    P2 = Decrypt(C, K, N, R=R, W=W)
    print("Decrypted :", P2)

    correctness_test(R=R, W=W, tests=200)
    perf_benchmark(R=R, W=W, trials=2000)

    AvalanchePerRound_PureSPN(R=R, trials=80, W=W)

    # BIC quick run
    K2, N2 = os.urandom(16), os.urandom(16)
    T, ROUND_KEY, ROUND_PERM = init_frozen(K2, N2, R, W)
    measure_bic(P=os.urandom(16), T=T, ROUND_KEY=ROUND_KEY, ROUND_PERM=ROUND_PERM, R=R, trials=40, bits_to_flip=32)

