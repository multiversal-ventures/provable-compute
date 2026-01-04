# Proof Backend Analysis

**Status:** Draft for Joint Decision
**Last Updated:** 2026-01-04

---

## Overview

This document analyzes proof system options for the SDK. The choice of backend affects:
- What computations can be proved
- Performance characteristics
- Verification guarantees
- Development complexity

---

## Candidates

### 1. Z3 (SMT Solver)

**What it is:** Satisfiability Modulo Theories solver from Microsoft Research

**Best for:** Arithmetic, comparisons, boolean logic

```smt2
; Example: Prove income stability calculation
(declare-const y1 Real)
(declare-const y2 Real)
(declare-const pct_change Real)

; Input constraints
(assert (= y1 60000.0))
(assert (= y2 50000.0))

; Derivation
(assert (= pct_change (/ (- y1 y2) y2)))

; Threshold check
(assert (>= pct_change -0.05))

(check-sat)  ; Returns: sat
```

| Aspect | Assessment |
|--------|------------|
| **Maturity** | Very mature (15+ years) |
| **Speed** | Fast (ms for simple proofs) |
| **Arithmetic** | Excellent |
| **Expressiveness** | Limited (no induction, recursion) |
| **Learning curve** | Low |
| **Integration** | Python bindings available |

**Verdict:** Strong choice for P0 arithmetic operations

---

### 2. Lean 4

**What it is:** Modern proof assistant with dependent types

**Best for:** Complex logic, custom theories, extensibility

```lean
-- Example: Prove income stability
theorem income_stable (y1 y2 : Float) (h1 : y1 = 60000) (h2 : y2 = 50000) :
  (y1 - y2) / y2 >= -0.05 := by
  simp [h1, h2]
  norm_num
```

| Aspect | Assessment |
|--------|------------|
| **Maturity** | Newer but production-ready |
| **Speed** | Moderate |
| **Arithmetic** | Good (with tactics) |
| **Expressiveness** | Very high |
| **Learning curve** | Steep |
| **Integration** | CLI-based, improving |

**Verdict:** Good for future complex specifications

---

### 3. Coq

**What it is:** Battle-tested proof assistant

**Best for:** High-assurance, formal certification

```coq
(* Example: Prove income stability *)
Theorem income_stable : forall y1 y2 : R,
  y1 = 60000 -> y2 = 50000 ->
  (y1 - y2) / y2 >= -0.05.
Proof.
  intros. subst. lra.
Qed.
```

| Aspect | Assessment |
|--------|------------|
| **Maturity** | Very mature (30+ years) |
| **Speed** | Slower |
| **Arithmetic** | Good |
| **Expressiveness** | Very high |
| **Learning curve** | Very steep |
| **Integration** | CLI-based |

**Verdict:** Overkill for current needs, consider for high-assurance future

---

### 4. Custom DSL

**What it is:** Purpose-built verification language

| Aspect | Assessment |
|--------|------------|
| **Maturity** | N/A (would need to build) |
| **Speed** | Could optimize |
| **Arithmetic** | As needed |
| **Expressiveness** | As needed |
| **Learning curve** | Low (we control it) |
| **Integration** | Native |

**Verdict:** Not recommended for MVP - build/maintain burden too high

---

## Comparison Matrix

| Feature | Z3 | Lean 4 | Coq | Custom |
|---------|-----|--------|-----|--------|
| P0 arithmetic | ✅ | ✅ | ✅ | ✅ |
| P1 functions (max, min) | ✅ | ✅ | ✅ | ✅ |
| P2 arrays | ⚠️ | ✅ | ✅ | ✅ |
| Proof generation speed | ⭐⭐⭐ | ⭐⭐ | ⭐ | ⭐⭐⭐ |
| Verification speed | ⭐⭐⭐ | ⭐⭐ | ⭐⭐ | ⭐⭐⭐ |
| Third-party verifiable | ✅ | ✅ | ✅ | ❌ |
| Ecosystem/tooling | ⭐⭐⭐ | ⭐⭐ | ⭐⭐ | ❌ |
| Team expertise needed | Low | High | High | Medium |

---

## Recommendation

### Phase 1: Z3 Only

Start with Z3 for the proof-of-concept:

- Covers all P0 expressions (arithmetic, comparisons, boolean)
- Fast enough for synchronous verification
- Well-documented, easy to integrate
- Proofs are machine-checkable by any Z3 installation

### Phase 2: Add Lean 4 (Future)

When/if we need:
- Recursive computations
- Array/list operations
- Custom domain theories
- Higher expressiveness

### Phase 3: Evaluate Coq (Future)

If customers require:
- Formal certification standards
- Defense/aerospace compliance
- Academic publication requirements

---

## Z3 Implementation Details

### SMT-LIB2 Format

The SDK will generate SMT-LIB2 format proofs:

```smt2
; Header
(set-logic QF_NRA)  ; Quantifier-free nonlinear real arithmetic

; Declarations
(declare-const input_y1 Real)
(declare-const input_y2 Real)
(declare-const derived_pct_change Real)
(declare-const output_is_stable Bool)

; Input bindings
(assert (= input_y1 60000.0))
(assert (= input_y2 50000.0))

; Derivations (the computation)
(assert (= derived_pct_change (/ (- input_y1 input_y2) input_y2)))
(assert (= output_is_stable (>= derived_pct_change -0.05)))

; Claim: output matches expected
(assert output_is_stable)

; Check satisfiability
(check-sat)
(get-model)
```

### Expression Translation

| SDK Expression | SMT-LIB2 |
|----------------|----------|
| `a + b` | `(+ a b)` |
| `a - b` | `(- a b)` |
| `a * b` | `(* a b)` |
| `a / b` | `(/ a b)` |
| `a >= b` | `(>= a b)` |
| `a && b` | `(and a b)` |
| `a \|\| b` | `(or a b)` |
| `!a` | `(not a)` |
| `a ? b : c` | `(ite a b c)` |
| `max(a, b)` | `(ite (>= a b) a b)` |
| `min(a, b)` | `(ite (<= a b) a b)` |
| `abs(a)` | `(ite (>= a 0) a (- a))` |

### Verification Flow

```
1. SDK receives: formulas + inputs + outputs
2. SDK generates: SMT-LIB2 script
3. SDK runs: z3 -smt2 script.smt2
4. Z3 returns: sat/unsat + model
5. SDK packages: script + result as ProofArtifact
6. Deep Symbolic: re-runs Z3, confirms result
```

---

## Open Questions

- [ ] **Z3 version pinning:** Which Z3 version to standardize on?
- [ ] **Floating point:** Use Real or Float64 in Z3?
- [ ] **Timeout handling:** What if Z3 times out on complex proofs?
- [ ] **Proof portability:** Can proofs be verified by other SMT solvers?
- [ ] **Lean timeline:** When would we need Lean capabilities?
