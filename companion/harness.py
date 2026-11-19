"""Exact executable examples; scope and exclusions are in README.md."""
from fractions import Fraction as F
from itertools import product
import argparse
import json
import sys

def check(condition, message=""):
    """Keep checks active even when Python optimisation removes assert statements."""
    if not condition:
        raise AssertionError(message)

def membership(labels):
    return tuple(int(label == 0) for label in labels)


def persistent(labels):
    return all(membership(labels))


def decoder(readings, verdicts):
    if len(readings) != len(verdicts):
        raise ValueError("different carriers")
    out = {}
    for reading, verdict in zip(readings, verdicts):
        if reading in out and out[reading] != verdict:
            return None
        out[reading] = verdict
    return out


def sufficient(key, verdict):
    return decoder(key, verdict) is not None


def correct_decoder_exists(key, verdict):
    candidate = decoder(key, verdict)
    return candidate is not None


def dot(a, v):
    return sum(x*y for x, y in zip(a, v))


def kernel_basis(r):
    if len(r) != 2:
        raise ValueError("this model is two-dimensional")
    return ((F(1), F(0)), (F(0), F(1))) if not any(r) else ((-r[1], r[0]),)


def preserves(a, r):
    if not any(a):
        raise ValueError("C5 assumes a nonzero original functional")
    return all(dot(a, v) == 0 for v in kernel_basis(r))


def linear_fibre_readable(a, r, carrier):
    """C4 for the C5 pair on a finite carrier: is the verdict 1[a(v) != 0] decodable from r(v)?

    The carrier is finite and supplied by the caller; it does not stand for the whole real space.
    """
    carrier = tuple(carrier)
    readings = tuple(dot(r, v) for v in carrier)
    verdicts = tuple(int(dot(a, v) != 0) for v in carrier)
    return sufficient(readings, verdicts)


def proportional(a, r):
    if not any(a) or not any(r):
        return False
    j = next(i for i in range(2) if r[i] != 0)
    c = F(a[j], r[j])
    return c != 0 and all(a[i] == c*r[i] for i in range(2))


def restricted_readable(a, r, witnesses):
    witnesses = tuple(witnesses)  # read once: a one-shot iterator must not reach the domain empty
    if not witnesses or any(dot(a, v) == 0 for v in witnesses):
        raise ValueError("W0 must be a nonempty set of witnesses with nonzero original pairing")
    domain = sorted(set(witnesses) | {(0, 0)})
    return linear_fibre_readable(a, r, domain)


def loss_kind(a, r, witnesses):
    """Loss counted on the supplied set W0 only; it does not decide whether r is zero."""
    witnesses = tuple(witnesses)
    if not witnesses or any(dot(a, v) == 0 for v in witnesses):
        raise ValueError("nonempty set of original witnesses required")
    survives = [dot(r, v) != 0 for v in witnesses]
    if not any(survives):
        return "all selected witnesses lost"
    if not all(survives):
        return "partial"
    return "none"


def restart(capability, request):
    return capability or request


def t_W01_cancelled_seams():
    labels = ((0, 0), (1, 0), (1, -1))  # the three rows of the manuscript table
    check(tuple(membership(row) for row in labels) == ((1, 1), (0, 1), (0, 0)))
    check(tuple(map(persistent, labels)) == (True, False, False))
    check(tuple(map(sum, labels)) == (0, 1, 0))
    check(decoder(tuple(map(sum, labels)), tuple(map(persistent, labels))) is None)
    # All nine label pairs over {-1, 0, 1}: membership words repeat across
    # pairs, so a decoder from them is a property of the reading, not of distinct words, and the
    # decoder that is returned is applied to every pair.
    pairs = tuple(product((-1, 0, 1), repeat=2))
    words, verdicts = tuple(map(membership, pairs)), tuple(map(persistent, pairs))
    check(len(set(words)) < len(pairs), "membership words repeat on the nine pairs")
    found = decoder(words, verdicts)
    check(found is not None and all(found.get(w) == v for w, v in zip(words, verdicts)),
          "the membership decoder, applied, returns every verdict")
    check(decoder(tuple(map(sum, pairs)), verdicts) is None, "no decoder from the sum on the nine pairs")
    late = (0, 1)  # not a table row: admitted at the first seam, lost at the second
    check(membership(late) == (1, 0), late)
    check(not persistent(late), ("lost after an admitted first seam", late))
    for row in labels + (late,):
        check(persistent(row[::-1]) == persistent(row), ("reversed seam order", row))


def t_W02_sufficient_compression():
    key, q, mixed = (0, 1, 0, 1), (0, 1, 0, 1), (0, 0, 1, 1)
    check(sufficient(key, q) and len(set(key)) < len(key))
    check(not sufficient(key, mixed))
    # Bijective relabellings of the key, the complement among them: the verdict is still
    # decoded, now by a decoder other than the identity, and the mixed fibre stays mixed.
    for names in ((7, 3), (1, 0), ("x", "y")):
        renamed = tuple(names[k] for k in key)
        check(sufficient(renamed, q), ("relabelled key", renamed))
        check(not sufficient(renamed, mixed), ("relabelled key, mixed fibre", renamed))


def t_W03_exists_vs_chosen():
    key, q = (0, 0, 1, 1), (0, 0, 1, 1)
    check(correct_decoder_exists(key, q))
    # Fixed counterexample, not a test of any procedure that selects a decoder: one decoder
    # chosen in advance (constant 0) is wrong on this key although a correct decoder exists.
    chosen = {0: 0, 1: 0}
    check(tuple(chosen[k] for k in key) != q, "fixed counterexample decoder")
    # The operative existence test: every binary key and verdict on three elements.
    for k in product(range(2), repeat=3):
        for v in product(range(2), repeat=3):
            expected = all(k[i] != k[j] or v[i] == v[j] for i in range(3) for j in range(3))
            check(correct_decoder_exists(k, v) == expected)


def t_W04_linear_kernel_bridge():
    vectors = list(product(range(-2, 3), repeat=2))
    # Exact change of coordinates T(x, y) = (x + y, y). A functional c becomes
    # c o T^-1 = (c0, c1 - c0), so every pairing c(v) is unchanged.
    moved = [(x + y, y) for x, y in vectors]
    def pulled(c):
        return (c[0], c[1] - c[0])
    for a in vectors:
        if not any(a):
            continue
        for r in vectors:
            check(preserves(a, r) == proportional(a, r), (a, r))
            # C4 bridge on a finite carrier that holds 0 and the kernel vector (-r1, r0)
            # of every nonzero r here, and both basis vectors for r = 0: exact for this
            # population, not a proof over the real plane.
            readable = linear_fibre_readable(a, r, vectors)
            check(readable == preserves(a, r), ("bridge", a, r))
            scaled = (F(-3, 2)*r[0], F(-3, 2)*r[1])
            check(linear_fibre_readable(a, scaled, vectors) == preserves(a, scaled) == readable,
                  ("rational scaling", a, r))
            check(linear_fibre_readable(pulled(a), pulled(r), moved) == preserves(pulled(a), pulled(r))
                  == readable, ("basis change", a, r))
    check(preserves((2, 4), (1, 2)))
    check(not preserves((1, 0), (0, 0)))
    check(not preserves((1, 0), (0, 1)))
    # The change applied to the carrier and to a, with r left in the old coordinates,
    # is a different reading and a different verdict.
    a, r = (1, 0), (2, 0)
    check(linear_fibre_readable(pulled(a), pulled(r), moved), ("consistent change", a, r))
    check(not linear_fibre_readable(pulled(a), r, moved), ("r not transformed", a, r))


def t_W05_restricted_zero_fibre():
    a, r, w0 = (1, 0), (0, 1), [(1, 1)]
    check(restricted_readable(a, r, w0))
    check(not proportional(a, r))
    check(not restricted_readable(a, (0, 0), w0))
    check(not restricted_readable(a, r, [(1, 0), (1, 1)]))
    check(not restricted_readable(a, r, iter([(1, 0), (1, 1)])), "a one-shot iterator of W0 is read once")
    try:
        restricted_readable(a, (0, 0), [])
    except ValueError:
        pass
    else:
        check(False, "an empty W0 is refused: the criterion is stated for a nonempty selected set")


def t_W06_selected_vs_global_loss():
    a, w0 = (1, 0), [(1, 0), (1, 1)]
    check(loss_kind(a, (0, 1), w0) == "partial")
    check(loss_kind(a, (1, 0), w0) == "none")
    # Every selected witness lost while r is nonzero: W0 = {(1, -2)} lies in ker r,
    # and the a-witness (1, 0) outside W0 keeps a nonzero transported pairing.
    r = (-2, -1)
    check(loss_kind(a, r, [(1, -2)]) == "all selected witnesses lost", ("selected loss, r nonzero", r))
    check(loss_kind(a, r, [(1, 0)]) == "none", ("another a-witness survives", r))
    # Global loss is a separate regime: r = 0 loses every a-witness of a carrier whose
    # a-witnesses span the plane, hence every a-witness; the nonzero r above does not.
    every = [v for v in product(range(-2, 3), repeat=2) if dot(a, v) != 0]
    check(loss_kind(a, (0, 0), every) == "all selected witnesses lost", "r = 0 loses every witness")
    check(loss_kind(a, r, every) == "partial", ("nonzero r is not global loss", r))
    for witnesses, transported in ((w0, (0, 1)), (w0, (1, 0)), ([(1, -2), (-1, 2)], r)):
        check(loss_kind(a, transported, witnesses[::-1]) == loss_kind(a, transported, witnesses),
              ("reordered W0", witnesses, transported))


def t_W07_silent_intervention():
    check(tuple(restart(c, p) for c, p in product((False, True), repeat=2)) == (False, True, True, True))
    check(restart(False, True) == restart(True, True))
    check(restart(False, False) != restart(True, False))
def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--teeth", action="store_true", help="the default action; kept for the documented commands")
    parser.add_argument("--json", type=str, help="write named outcomes to this file")
    args = parser.parse_args()
    tests = sorted((n, f) for n, f in globals().items() if n.startswith("t_") and callable(f))
    results = []
    for name, test in tests:
        try:
            test()
        except AssertionError as exc:
            results.append({"name": name, "status": "FAIL", "detail": str(exc)})
            print("FAIL " + name + ": " + str(exc))
        except Exception as exc:
            results.append({"name": name, "status": "ERROR", "detail": repr(exc)})
            print("ERROR " + name + ": " + repr(exc))
        else:
            results.append({"name": name, "status": "PASS"})
    passed = sum(r["status"] == "PASS" for r in results)
    print("teeth: %d/%d" % (passed, len(tests)))
    if args.json:
        from pathlib import Path
        Path(args.json).write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")
    return 0 if tests and passed == len(tests) else 1

if __name__ == "__main__":
    sys.exit(main())
