"""
Z3 Theorem Templates for Regular Expressions (RE)
==================================================
Reusable templates for proving/refuting theorems about regular languages
using Z3's built-in theory of strings and regular expressions
(SMT-LIB `Seq`/`RegLan` theory, exposed in z3py as `Re`, `InRe`, etc.).

Install:
    pip install z3-solver --break-system-packages

Core idea behind every template here:
    A "theorem about regex languages" (equality, containment, emptiness,
    disjointness, universality...) is turned into a SATISFIABILITY query
    for a *witness string*. If Z3 reports UNSAT, no counterexample exists,
    so the theorem holds. If Z3 reports SAT, the model gives you a concrete
    counterexample string.
"""

from z3 import (
    String, Solver, sat, unsat, InRe, Re, Union, Intersect, Complement,
    Star, Plus, Option, Loop, Range, Concat, Full, Empty, AllChar,
    ReSort, StringSort, Length, Not, Xor, And, Or
)

# ---------------------------------------------------------------------------
# 0. BUILDING BLOCKS — how to construct regex terms
# ---------------------------------------------------------------------------
# Re("abc")            literal string as a regex
# Union(r1, r2, ...)   r1 | r2 | ...
# Concat(r1, r2, ...)  r1 r2 ...
# Star(r)              r*
# Plus(r)              r+
# Option(r)            r?
# Loop(r, lo, hi)       r{lo,hi}
# Range("a", "z")       [a-z]
# Complement(r)         ¬r   (everything NOT matched by r)
# Intersect(r1, r2)     r1 & r2
# AllChar(ReSort(StringSort()))  any single character  (the "." of regex)
# Full(ReSort(StringSort()))     Sigma*  (matches everything)
# Empty(ReSort(StringSort()))    the empty language (matches nothing)
#
# Membership: InRe(s, r)  -- "string s matches regex r"


# ---------------------------------------------------------------------------
# TEMPLATE 1 — Membership: does a *specific* string match a regex?
# ---------------------------------------------------------------------------
def template_membership(concrete_string: str, r):
    """
    THEOREM: concrete_string ∈ L(r)

    Proof strategy: assert the string equals a literal and assert membership;
    ask Z3 to check satisfiability of both together.
    """
    s = String("s")
    solver = Solver()
    solver.add(s == concrete_string)
    solver.add(InRe(s, r))
    holds = solver.check() == sat
    return holds


# ---------------------------------------------------------------------------
# TEMPLATE 2 — Emptiness: is L(r) the empty language?
# ---------------------------------------------------------------------------
def template_is_empty(r):
    """
    THEOREM: L(r) = ∅

    Proof strategy: try to find ANY string matching r. If unsat, no such
    string exists, so the language is empty.
    """
    s = String("witness")
    solver = Solver()
    solver.add(InRe(s, r))
    result = solver.check()
    if result == unsat:
        return True, None
    return False, solver.model()[s]


# ---------------------------------------------------------------------------
# TEMPLATE 3 — Universality: does r match every possible string (Sigma*)?
# ---------------------------------------------------------------------------
def template_is_universal(r):
    """
    THEOREM: L(r) = Σ*

    Proof strategy: L(r) is universal iff its complement is empty.
    Reduces directly to Template 2 applied to Complement(r).
    """
    return template_is_empty(Complement(r))


# ---------------------------------------------------------------------------
# TEMPLATE 4 — Disjointness: do two regexes share no matching string?
# ---------------------------------------------------------------------------
def template_disjoint(r1, r2):
    """
    THEOREM: L(r1) ∩ L(r2) = ∅

    Proof strategy: emptiness of the intersection regex, via Template 2.
    """
    return template_is_empty(Intersect(r1, r2))


# ---------------------------------------------------------------------------
# TEMPLATE 5 — Containment (subset): is every string matched by r1 also
#              matched by r2?
# ---------------------------------------------------------------------------
def template_subset(r1, r2):
    """
    THEOREM: L(r1) ⊆ L(r2)

    Proof strategy: look for a witness string that is in L(r1) but NOT in
    L(r2). UNSAT => containment holds. SAT => model is a counterexample
    string that breaks the containment.
    """
    s = String("witness")
    solver = Solver()
    solver.add(InRe(s, r1))
    solver.add(Not(InRe(s, r2)))
    result = solver.check()
    if result == unsat:
        return True, None
    return False, solver.model()[s]


# ---------------------------------------------------------------------------
# TEMPLATE 6 — Equivalence: do two regexes describe exactly the same
#              language?
# ---------------------------------------------------------------------------
def template_equivalent(r1, r2):
    """
    THEOREM: L(r1) = L(r2)

    Proof strategy: look for a witness string in the symmetric difference
    (matches exactly one of the two regexes). UNSAT => same language.
    SAT => model is a distinguishing string.
    """
    s = String("witness")
    solver = Solver()
    solver.add(Xor(InRe(s, r1), InRe(s, r2)))
    result = solver.check()
    if result == unsat:
        return True, None
    return False, solver.model()[s]


# ---------------------------------------------------------------------------
# TEMPLATE 7 — Constrained synthesis: find a string that matches a regex
#              AND satisfies extra side constraints (length, prefix, etc.)
# ---------------------------------------------------------------------------
def template_constrained_match(r, min_len=None, max_len=None, extra=None):
    """
    THEOREM (existential): ∃ s . s ∈ L(r) ∧ extra-constraints(s)

    Useful for test-case generation, e.g. "give me a string that matches
    this regex and is between 5 and 8 characters long".

    `extra` is an optional list of functions taking the string term `s`
    and returning a z3 BoolRef constraint (e.g. lambda s: Length(s) > 3).
    """
    s = String("s")
    solver = Solver()
    solver.add(InRe(s, r))
    if min_len is not None:
        solver.add(Length(s) >= min_len)
    if max_len is not None:
        solver.add(Length(s) <= max_len)
    if extra:
        for constraint_fn in extra:
            solver.add(constraint_fn(s))
    if solver.check() == sat:
        return solver.model()[s]
    return None


# ---------------------------------------------------------------------------
# TEMPLATE 8 — Non-membership: prove a string can NEVER match a regex
#              under additional assumptions (useful for security-style
#              "this input is always rejected" proofs).
# ---------------------------------------------------------------------------
def template_never_matches(r, assumptions):
    """
    THEOREM: ∀ s . assumptions(s) ⇒ s ∉ L(r)

    Proof strategy: negate the theorem (assumptions(s) AND s ∈ L(r)) and
    check unsatisfiability. UNSAT => theorem holds for all such strings.
    """
    s = String("s")
    solver = Solver()
    for a in assumptions:
        solver.add(a(s))
    solver.add(InRe(s, r))
    result = solver.check()
    if result == unsat:
        return True, None
    return False, solver.model()[s]


# ---------------------------------------------------------------------------
# DEMO — worked examples exercising every template above
# ---------------------------------------------------------------------------
if __name__ == "__main__":
    # A regex for lowercase words of length >= 1: [a-z]+
    lower_word = Plus(Range("a", "z"))

    # A regex for "a" followed by zero or more "b"s, then "c": a b* c
    abc_pattern = Concat(Re("a"), Star(Re("b")), Re("c"))

    # A regex equivalent to abc_pattern but written differently:
    # a(b|bb)*c is NOT equivalent (it forces pairs of b or skips), good
    # counterexample-producing comparison.
    abc_pattern_alt = Concat(Re("a"), Star(Union(Re("b"), Re("bb"))), Re("c"))

    print("Template 1 — membership:")
    print("  'hello' in [a-z]+   ->", template_membership("hello", lower_word))
    print("  'Hi9' in [a-z]+     ->", template_membership("Hi9", lower_word))

    print("\nTemplate 2 — emptiness:")
    contradiction = Intersect(Re("abc"), Re("xyz"))
    print("  L(abc & xyz) empty? ->", template_is_empty(contradiction))

    print("\nTemplate 3 — universality:")
    sigma_star = Star(AllChar(ReSort(StringSort())))
    print("  Star(AllChar) universal? ->", template_is_universal(sigma_star))
    print("  [a-z]+ universal?        ->", template_is_universal(lower_word))

    print("\nTemplate 4 — disjointness:")
    print("  [a-z]+  vs  'abc'  disjoint? ->",
          template_disjoint(lower_word, Re("abc")))

    print("\nTemplate 5 — containment:")
    print("  L('abc') subset of L([a-z]+)? ->",
          template_subset(Re("abc"), lower_word))

    print("\nTemplate 6 — equivalence:")
    print("  abc_pattern == abc_pattern_alt? ->",
          template_equivalent(abc_pattern, abc_pattern_alt))

    print("\nTemplate 7 — constrained synthesis:")
    match = template_constrained_match(
        lower_word, min_len=5, max_len=8,
        extra=[lambda s: s != "hello"]
    )
    print("  A 5-8 char lowercase word != 'hello':", match)

    print("\nTemplate 8 — never matches (guarded property):")
    # Prove: any string of length < 3 can never match abc_pattern (needs
    # at least 'a' + 'c' = length >= 2, so try length < 2 to guarantee it)
    ok, cex = template_never_matches(
        abc_pattern, assumptions=[lambda s: Length(s) < 2]
    )
    print("  strings shorter than 2 never match 'a b* c'? ->", ok, cex)


# ---------------------------------------------------------------------------
# APPENDIX — raw SMT-LIB2 equivalents (for use outside Python, e.g. z3 CLI)
# ---------------------------------------------------------------------------
"""
; Membership
(declare-const s String)
(assert (= s "hello"))
(assert (str.in_re s (re.+ (re.range "a" "z"))))
(check-sat)

; Equivalence via symmetric difference (unsat = equivalent)
(declare-const w String)
(assert (xor (str.in_re w R1) (str.in_re w R2)))
(check-sat)

; Subset via counterexample search (unsat = subset holds)
(declare-const w String)
(assert (str.in_re w R1))
(assert (not (str.in_re w R2)))
(check-sat)

; Emptiness (unsat = language is empty)
(declare-const w String)
(assert (str.in_re w R))
(check-sat)
"""
