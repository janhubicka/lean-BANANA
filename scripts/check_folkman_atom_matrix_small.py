#!/usr/bin/env python3
"""Independent finite sanity checks for Folkman atom-matrix reconstruction.

This regression supplements, but does not replace, a kernel-checked Lean proof.
"""

def check_function_space(l: int, r: int) -> tuple[int, int]:
    left, right = 1 << l, 1 << r
    count = 0
    for values in range(1 << (left * right)):
        def beta(x: int, y: int) -> int:
            return (values >> (x * right + y)) & 1
        if any(beta(x ^ xp, y) != (beta(x, y) ^ beta(xp, y))
               for x in range(left) for xp in range(left) for y in range(right)):
            continue
        if any(beta(x, y ^ yp) != (beta(x, y) ^ beta(x, yp))
               for x in range(left) for y in range(right) for yp in range(right)):
            continue
        count += 1
        matrix = sum(beta(1 << i, 1 << j) << (i * r + j)
                     for i in range(l) for j in range(r))
        for x in range(left):
            for y in range(right):
                reconstructed = 0
                for i in range(l):
                    for j in range(r):
                        if (x >> i) & 1 and (y >> j) & 1:
                            reconstructed ^= (matrix >> (i * r + j)) & 1
                assert beta(x, y) == reconstructed, (l, r, values, x, y)
    assert count == 1 << (l * r), (l, r, count)
    return 1 << (left * right), count


def main() -> None:
    tested, additive = 0, 0
    for l in range(3):
        for r in range(3):
            n, k = check_function_space(l, r)
            tested += n
            additive += k
    matrix_cases = 0
    for l in range(4):
        for r in range(4):
            for bits in range(1 << (l * r)):
                for x in range(1 << l):
                    for y in range(1 << r):
                        direct = sum((bits >> (i * r + j)) & 1
                                     for i in range(l) if x >> i & 1
                                     for j in range(r) if y >> j & 1) & 1
                        atom_sum = 0
                        for i in range(l):
                            if x >> i & 1:
                                for j in range(r):
                                    if y >> j & 1:
                                        atom_sum ^= (bits >> (i * r + j)) & 1
                        assert direct == atom_sum
                        matrix_cases += 1
    print(f"Folkman atom-matrix checks passed: {tested} pairing functions, "
          f"{additive} biadditive, {matrix_cases} matrix/support cases")


if __name__ == "__main__":
    main()
