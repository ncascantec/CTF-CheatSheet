"""
Full CTF Reverse-Engineering Example: Solving a Crackme's Flag with Z3 RE
============================================================================

SCENARIO
--------
You've reversed a "baby_re" crackme in Ghidra. The decompiled checker
(cleaned up from the actual disassembly, which used a mix of strncmp,
a range-compare loop with cmp/jae/jbe, a strstr call, and a sliding
window loop) looks like this:

    int check(char *buf) {
        if (strlen(buf) != 20)               return 0;   // fixed length
        if (strncmp(buf, "CTF{", 4) != 0)    return 0;   // fixed prefix
        if (buf[19] != '}')                  return 0;   // fixed suffix

        // indices 4..18 (15 chars) must be uppercase letters or digits
        for (int i = 4; i < 19; i++) {
            if (!isupper(buf[i]) && !isdigit(buf[i]))
                return 0;
        }

        // anti-bruteforce trick #1: the substring "Z3" must appear
        if (!strstr(buf, "Z3"))              return 0;

        // anti-bruteforce trick #2: no 3 consecutive digits anywhere
        for (int i = 0; i < 18; i++) {
            if (isdigit(buf[i]) && isdigit(buf[i+1]) && isdigit(buf[i+2]))
                return 0;
        }

        return 1;  // valid flag
    }

Each of these branches maps directly onto one of the RE templates from
the earlier file. We don't brute force anything -- we just describe the
*shape* of a valid input and let Z3 find one.
"""

from z3 import (
    String, Solver, sat, InRe, Re, Union, Concat, Star, Loop, Range,
    Complement, AllChar, ReSort, StringSort, Length
)

s = String("flag")
solver = Solver()

# ---------------------------------------------------------------------
# 1) length check  ->  Length(s) == N
# ---------------------------------------------------------------------
solver.add(Length(s) == 20)

# ---------------------------------------------------------------------
# 2) fixed prefix / body character-class / fixed suffix
#    -> Concat(literal, Loop(char_class, k, k), literal)
# ---------------------------------------------------------------------
prefix = Re("CTF{")
suffix = Re("}")

body_char = Union(Range("A", "Z"), Range("0", "9"))   # isupper() || isdigit()
body = Loop(body_char, 15, 15)                        # exactly 15 chars (idx 4..18)

shape = Concat(prefix, body, suffix)
solver.add(InRe(s, shape))

# ---------------------------------------------------------------------
# 3) "must contain Z3" trick  ->  Sigma* Z3 Sigma*
# ---------------------------------------------------------------------
any_chars = Star(AllChar(ReSort(StringSort())))
contains_z3 = Concat(any_chars, Re("Z3"), any_chars)
solver.add(InRe(s, contains_z3))

# ---------------------------------------------------------------------
# 4) "must NOT contain 3 consecutive digits" trick
#    -> Complement( Sigma* [0-9][0-9][0-9] Sigma* )
# ---------------------------------------------------------------------
digit = Range("0", "9")
three_digits_anywhere = Concat(any_chars, Concat(digit, digit, digit), any_chars)
solver.add(InRe(s, Complement(three_digits_anywhere)))

# ---------------------------------------------------------------------
# solve
# ---------------------------------------------------------------------
if solver.check() == sat:
    model = solver.model()
    flag = model[s].as_string()
    print("FLAG:", flag)
else:
    print("UNSAT -- go re-check the extracted constraints, "
          "this almost always means a mis-reversed branch, not "
          "an unsolvable challenge.")


# ===========================================================================
# BONUS -- when the checker is a raw hand-rolled DFA instead of clean regex
# ===========================================================================
# Some crackmes don't have clean per-character checks -- they implement a
# state machine directly (a `state = table[state][c]` walk through the
# string, common in obfuscated / VM-based challenges). You COULD write the
# equivalent Re() by hand (regular languages == DFAs, by Kleene's theorem),
# but for anything beyond a few states that's tedious and error-prone.
# It's usually faster to encode the transition table directly:

def solve_dfa(transitions, alphabet, start_state, accept_states, length):
    """
    transitions:   dict[(state, char)] -> next_state, reversed from the
                   binary's jump/lookup table.
    alphabet:      iterable of allowed single characters.
    start_state:   the DFA's initial state (int).
    accept_states: set of accepting states (int).
    length:        exact length of the string to solve for.

    Returns a matching string, or None if no such string exists.
    """
    from z3 import Int, Or, And, IntVal

    chars = [String(f"c{i}") for i in range(length)]
    states = [Int(f"st{i}") for i in range(length + 1)]

    dsolver = Solver()
    dsolver.add(states[0] == start_state)

    for i in range(length):
        dsolver.add(Length(chars[i]) == 1)
        options = []
        for (st, ch), nxt in transitions.items():
            options.append(
                And(states[i] == st, chars[i] == ch, states[i + 1] == nxt)
            )
        dsolver.add(Or(options))

    dsolver.add(Or([states[length] == acc for acc in accept_states]))

    if dsolver.check() == sat:
        m = dsolver.model()
        return "".join(m[c].as_string() for c in chars)
    return None


if __name__ == "__main__":
    # Tiny illustrative DFA: accepts exactly "ab" repeated any number of
    # times over a fixed length -- reversed from a hypothetical 3-state
    # transition table found in the binary.
    demo_transitions = {
        (0, "a"): 1,
        (1, "b"): 0,
    }
    result = solve_dfa(
        demo_transitions,
        alphabet=["a", "b"],
        start_state=0,
        accept_states={0},
        length=6,
    )
    print("DFA-derived string:", result)
