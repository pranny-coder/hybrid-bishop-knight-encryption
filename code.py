import hashlib
import os
import random
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

# ============================================================
# SBOX and inverse SBOX (4-bit)
# You can replace with your fixed SBOX, but this one is valid.
# ============================================================

SBOX = [0x6, 0x4, 0xC, 0x5,
        0x0, 0x7, 0x2, 0xE,
        0x1, 0xF, 0x3, 0xD,
        0x8, 0xA, 0x9, 0xB]

INV_SBOX = [0] * 16
for i, v in enumerate(SBOX):
    INV_SBOX[v] = i

# ============================================================
# Chess move tables
# MOVE_K32 : (±3,±2) and (±2,±3)
# MOVE_B2  : (±2,±2)
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
TABLE_B2 = BuildMoveTable(MOVE_B2)

def GetMoves(step_j: int, current_sq: int, mode: int) -> List[int]:
    # mode = 0 initially, flips when round % 3 == 0
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

# ============================================================
# 128-bit permutations
# We generate a list of deterministic permutations.
# Each perm is perm[0..127], mapping output_bit_index -> input_bit_index
# ============================================================

def generate_permutations(num: int = 128, seed: bytes = b"PERMUTATIONS_SEED") -> List[List[int]]:
    perms = []
    base = list(range(128))
    for i in range(num):
        rnd = random.Random(BitsToInt(H(seed + i.to_bytes(4, "big"))))
        p = base[:]
        rnd.shuffle(p)
        perms.append(p)
    return perms

PERMUTATIONS = generate_permutations(num=256)  # feel free to increase

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
    # NOTE:
    # Our perm is output->input mapping.
    # If ApplyPerm(out)=bits[perm[out]], then inverse should satisfy
    # ApplyPerm(inv, ApplyPerm(perm, bits)) == bits
    # The above inv creation works for that.
    return inv

# ============================================================
# Key schedule init() (from PDF)
# ============================================================

def init(K: bytes, N: bytes, R: int, W: int):
    seed = H(K + N)
    start_sq = BitsToInt(seed) % 64
    T = FirstBits(seed, 128)

    ROUND_KEY = [None] * (R + 1)   # 1..R
    ROUND_PERM = [None] * (R + 1)  # 1..R

    mode = 0

    for r in range(1, R + 1):
        if r % 3 == 0:
            mode ^= 1

        current_sq = start_sq
        walk_bytes = bytearray()

        for j in range(1, W + 1):
            # h = H( K || N || r || j || T )
            h = H(K + N + r.to_bytes(4, "big") + j.to_bytes(4, "big") + T)

            moves = GetMoves(j, current_sq, mode)

            if not moves:
                # fallback: union of both
                moves = list(set(TABLE_K32[current_sq] + TABLE_B2[current_sq]))

            idx = BitsToInt(h) % len(moves)
            next_sq = moves[idx]

            delta = current_sq ^ next_sq  # 0..63
            walk_bytes.append(delta & 0xFF)

            current_sq = next_sq

        round_hash = H(K + N + r.to_bytes(4, "big") + bytes(walk_bytes))
        ROUND_KEY[r] = FirstBits(round_hash, 128)

        p_idx = BitsToInt(round_hash) % len(PERMUTATIONS)
        ROUND_PERM[r] = PERMUTATIONS[p_idx]

    return T, ROUND_KEY, ROUND_PERM

# ============================================================
# SPN Encrypt / Decrypt (128-bit block)
# ============================================================

def Encrypt(P: bytes, K: bytes, N: bytes, R: int = 10, W: int = 32) -> bytes:
    assert len(P) == 16, "Plaintext must be exactly 16 bytes (128-bit)"
    T, ROUND_KEY, ROUND_PERM = init(K, N, R, W)

    STATE = XOR(XOR(P, ROUND_KEY[1]), T)

    for r in range(1, R + 1):
        STATE = XOR(STATE, ROUND_KEY[r])

        nibbles = split_nibbles(STATE)
        nibbles = [SBOX[x] for x in nibbles]
        STATE = join_nibbles(nibbles)

        STATE = ApplyPerm(ROUND_PERM[r], STATE)

    C = XOR(XOR(STATE, ROUND_KEY[R]), T)
    return C

def Decrypt(C: bytes, K: bytes, N: bytes, R: int = 10, W: int = 32) -> bytes:
    assert len(C) == 16, "Ciphertext must be exactly 16 bytes (128-bit)"
    T, ROUND_KEY, ROUND_PERM = init(K, N, R, W)

    STATE = XOR(XOR(C, T), ROUND_KEY[R])

    for r in range(R, 0, -1):
        invp = InversePerm(ROUND_PERM[r])
        STATE = ApplyPerm(invp, STATE)

        nibbles = split_nibbles(STATE)
        nibbles = [INV_SBOX[x] for x in nibbles]
        STATE = join_nibbles(nibbles)

        STATE = XOR(STATE, ROUND_KEY[r])

    P = XOR(XOR(STATE, T), ROUND_KEY[1])
    return P

# ============================================================
# Encrypt first k rounds (for Avalanche Test)
# ============================================================

def EncryptKRounds(P: bytes, K: bytes, N: bytes, k: int, R: int = 10, W: int = 32) -> bytes:
    assert 1 <= k <= R
    T, ROUND_KEY, ROUND_PERM = init(K, N, R, W)

    STATE = XOR(XOR(P, ROUND_KEY[1]), T)

    for r in range(1, k + 1):
        STATE = XOR(STATE, ROUND_KEY[r])

        nibbles = split_nibbles(STATE)
        nibbles = [SBOX[x] for x in nibbles]
        STATE = join_nibbles(nibbles)

        STATE = ApplyPerm(ROUND_PERM[r], STATE)

    # same final mixing style but only upto k (for consistency in measuring diffusion)
    return STATE

def flip_one_random_bit(block16: bytes) -> bytes:
    b = bytearray(block16)
    bitpos = random.randrange(128)
    byte_i = bitpos // 8
    bit_i = 7 - (bitpos % 8)
    b[byte_i] ^= (1 << bit_i)
    return bytes(b)

# ============================================================
# Avalanche test (from PDF)
# ============================================================

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

# ============================================================
# Quick Demo
# ============================================================

if __name__ == "__main__":
    K = b"THIS_IS_16_BYTEK"   # 16 bytes
    N = b"THIS_IS_16_BYTEN"   # 16 bytes

    P = b"HelloChessCipher!"  # 16 bytes
    print("Plaintext :", P)

    C = Encrypt(P, K, N, R=10, W=32)
    print("Ciphertext:", C.hex())

    P2 = Decrypt(C, K, N, R=10, W=32)
    print("Decrypted :", P2)

    print("\nAvalanche Test:")
    AvalanchePerRound(R=10, trials=100, W=32)
