import hashlib
import os
import random
from typing import List, Tuple
import time
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
    # 16 bytes -> 32 nibbles (4-bit values)
    nibbles = []
    for byte in block16:
        nibbles.append((byte >> 4) & 0xF)
        nibbles.append(byte & 0xF)
    return nibbles

def join_nibbles(nibbles: List[int]) -> bytes:
    # 32 nibbles -> 16 bytes
    out = bytearray(16)
    for i in range(16):
        hi = nibbles[2*i] & 0xF
        lo = nibbles[2*i + 1] & 0xF
        out[i] = (hi << 4) | lo
    return bytes(out)

def bytes_to_bits(block16: bytes) -> List[int]:
    # 16 bytes -> 128 bits (big endian within each byte)
    bits = []
    for byte in block16:
        for k in range(7, -1, -1):
            bits.append((byte >> k) & 1)
    return bits

def bits_to_bytes(bits: List[int]) -> bytes:
    # 128 bits -> 16 bytes
    out = bytearray(16)
    for i in range(16):
        v = 0
        for k in range(8):
            v = (v << 1) | (bits[i*8 + k] & 1)
        out[i] = v
    return bytes(out)

def hamming_distance(a: bytes, b: bytes) -> int:
    return sum((x ^ y).bit_count() for x, y in zip(a, b))

SBOX = [0x6, 0x4, 0xC, 0x5,
        0x0, 0x7, 0x2, 0xE,
        0x1, 0xF, 0x3, 0xD,
        0x8, 0xA, 0x9, 0xB]

INV_SBOX = [0] * 16
for i, v in enumerate(SBOX):
    INV_SBOX[v] = i
    
#K32 moves: (±3,±2) and (±2,±3)
MOVE_K32 = [
    (3, 2), (3, -2), (-3, 2), (-3, -2),
    (2, 3), (2, -3), (-2, 3), (-2, -3)
]

# B2 moves: diagonal (±2, ±2)
MOVE_B2 = [
    (2, 2), (2, -2), (-2, 2), (-2, -2)
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
TABLE_B2 = BuildMoveTable(MOVE_B2)

def GetMoves(step_j: int, current_sq: int, mode: int) -> List[int]:
    if mode == 0:
        if step_j % 2 == 1:
            return TABLE_K32[current_sq]
        else:
            return TABLE_B2[current_sq]
    else:
        if step_j % 2 == 0:
            return TABLE_K32[current_sq]
        else:
            return TABLE_B2[current_sq]

def generate_permutations(num: int = 128, seed: bytes = b"PERMUTATIONS_SEED") -> List[List[int]]:
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

def init(K: bytes, N: bytes, R: int, W: int):
    seed = H(K + N)
    start_sq = BitsToInt(seed) % 64
    T = FirstBits(seed, 128)

    ROUND_KEY = [None] * (R + 1)
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
    T, ROUND_KEY, ROUND_PERM = init(K, N, R, W)
    return T, ROUND_KEY, ROUND_PERM

def Encrypt(P: bytes, K: bytes, N: bytes, R: int = 10, W: int = 32) -> bytes:
    assert len(P) == 16
    T, ROUND_KEY, ROUND_PERM = init(K, N, R, W)

    STATE = XOR(P, T)

    for r in range(1, R + 1):
        STATE = XOR(STATE, ROUND_KEY[r])

        nibbles = split_nibbles(STATE)
        nibbles = [SBOX[x] for x in nibbles]
        STATE = join_nibbles(nibbles)

        STATE = ApplyPerm(ROUND_PERM[r], STATE)

    C = XOR(STATE, T)
    return C

def Decrypt(C: bytes, K: bytes, N: bytes, R: int = 10, W: int = 32) -> bytes:
    assert len(C) == 16
    T, ROUND_KEY, ROUND_PERM = init(K, N, R, W)

    STATE = XOR(C,T)

    for r in range(R, 0, -1):
        invp = InversePerm(ROUND_PERM[r])
        STATE = ApplyPerm(invp, STATE)

        nibbles = split_nibbles(STATE)
        nibbles = [INV_SBOX[x] for x in nibbles]
        STATE = join_nibbles(nibbles)

        STATE = XOR(STATE, ROUND_KEY[r])

    P = XOR(STATE,T)
    return P

def EncryptKRounds(P: bytes, K: bytes, N: bytes, k: int, R: int = 10, W: int = 32) -> bytes:
    assert 1 <= k <= R
    T, ROUND_KEY, ROUND_PERM = init(K, N, R, W)

    STATE = XOR(P, T)

    for r in range(1, k + 1):
        STATE = XOR(STATE, ROUND_KEY[r])

        nibbles = split_nibbles(STATE)
        nibbles = [SBOX[x] for x in nibbles]
        STATE = join_nibbles(nibbles)

        STATE = ApplyPerm(ROUND_PERM[r], STATE)

    return STATE

def EncryptKRoundsFrozen(P: bytes, T, ROUND_KEY, ROUND_PERM, k: int):
    STATE = XOR(P, T)

    for r in range(1, k + 1):
        STATE = XOR(STATE, ROUND_KEY[r])

        nibbles = split_nibbles(STATE)
        nibbles = [SBOX[x] for x in nibbles]
        STATE = join_nibbles(nibbles)

        STATE = ApplyPerm(ROUND_PERM[r], STATE)

    return STATE

def flip_one_random_bit(block16: bytes) -> bytes:
    b = bytearray(block16)
    bitpos = random.randrange(128)
    byte_i = bitpos // 8
    bit_i = 7 - (bitpos % 8)
    b[byte_i] ^= (1 << bit_i)
    return bytes(b)

def compute_full_correlation(C1: bytes, C2: bytes) -> float:
    bits1 = bytes_to_bits(C1)
    bits2 = bytes_to_bits(C2)

    n = len(bits1)
    mean1 = sum(bits1) / n
    mean2 = sum(bits2) / n
    numerator = sum((bits1[i] - mean1) * (bits2[i] - mean2) for i in range(n))
    denominator = (sum((bits1[i] - mean1) ** 2 for i in range(n)) * sum((bits2[i] - mean2) ** 2 for i in range(n))) ** 0.5
    if denominator == 0:
        return 0
    return numerator / denominator

def measure_bic(P: bytes, T: bytes, ROUND_KEY, ROUND_PERM, R: int, trials: int = 100):
    total_mean_corr = 0
    total_max_corr = 0
    total_pairs = 0

    for _ in range(trials):
        C1 = EncryptKRoundsFrozen(P, T, ROUND_KEY, ROUND_PERM, R)

        for i in range(128):
            P2 = flip_one_random_bit(P)
            C2 = EncryptKRoundsFrozen(P2, T, ROUND_KEY, ROUND_PERM, R)

            correlation = compute_full_correlation(C1, C2)

            total_mean_corr += correlation
            total_max_corr = max(total_max_corr, correlation)
            total_pairs += 1

    avg_mean_corr = total_mean_corr / total_pairs
    print(f"\nBIC Results: Mean correlation = {avg_mean_corr:.4f}, Max correlation = {total_max_corr:.4f}")

def AvalanchePerRound(R: int = 10, trials: int = 200, W: int = 32):
    K = os.urandom(16)
    N = os.urandom(16)

    for k in range(1, R + 1):
        total = 0
        for _ in range(trials):
            P = os.urandom(16)
            C1 = EncryptKRounds(P, K, N, k, R=R, W=W)

            P2 = flip_one_random_bit(P)
            C2 = EncryptKRounds(P2, K, N, k, R=R, W=W)

            total += hamming_distance(C1, C2)

        avg = total / trials
        print(f"Round {k:2d}: avg flipped bits = {avg:.2f} / 128")

def AvalanchePerRound_PureSPN(R: int = 10, trials: int = 200, W: int = 32):
    K = os.urandom(16)
    N = os.urandom(16)
    T, ROUND_KEY, ROUND_PERM = init_frozen(K, N, R, W)
    print("\nPure SPN Diffusion (SHA frozen):")

    for k in range(1, R + 1):
        total = 0
        for _ in range(trials):
            P = os.urandom(16)

            C1 = EncryptKRoundsFrozen(P, T, ROUND_KEY, ROUND_PERM, k)
            P2 = flip_one_random_bit(P)
            C2 = EncryptKRoundsFrozen(P2, T, ROUND_KEY, ROUND_PERM, k)

            total += hamming_distance(C1, C2)

        avg = total / trials
        print(f"Round {k:2d}: avg flipped bits = {avg:.2f} / 128")

if __name__ == "__main__":
    K = b"THIS_IS_16_BYTEK"
    N = b"THIS_IS_16_BYTEN"
    P = b"hellohellobabyga"
    print("Plaintext :", P)
    start = time.perf_counter()
    C = Encrypt(P, K, N, R=30, W=16)
    end = time.perf_counter()
    print("Ciphertext:", C.hex())
    P2 = Decrypt(C, K, N, R=30, W=16)
    print(f"\nTotal time taken: {end - start:.6f} seconds")
    print("Decrypted :", P2)
    T, ROUND_KEY, ROUND_PERM = init_frozen(K, N, R=30, W=32)
    print("\nAvalanche Test:")
    AvalanchePerRound(R=30, trials=100, W=32)
    AvalanchePerRound_PureSPN(R=30, trials=100, W=32)
    measure_bic(P, T, ROUND_KEY, ROUND_PERM, R=30, trials=100)

