# Fenero + Deep Symbolic: System Architecture (Concise)
## One-Sentence Summary
Fenero executes rules on data and proves it's correct; Deep Symbolic verifies the proof independently.



## What it should feel like
```
Rules Definer: "Here's the formula, I approved it"
               → Signature on formula
Data Source:   "Here's the data, I extracted it"
               → Hash + signature on data
Fenero:        "Here's the result, I computed it correctly"
               → Z3 proof + signature on execution
Deep Symbolic: "I verified the computation is mathematically correct"
               → Attestation + signature
Regulator:     "All signatures are valid, computation is proven correct"
               → Compliance determination
```


---

## Actors
| Actor | Role | Inputs | Outputs | Owns |
| ----- | ----- | ----- | ----- | ----- |
| **Rules Definer** | Create & approve rule formulas | Regulations | Rule formula + signature | Rules |
| **Data Source** | Extract & validate data | Documents | Data + hash + signature | Data |
| **Fenero** | Execute rule on data | Formula + data (signed) | Result + Z3 proof + signature | Execution proof |
| **Deep Symbolic** | Verify execution is correct | Result + proof + signatures | Attestation + signature | Verification |
| **Regulator** | Audit the decision | Attestation + proofs | Compliance determination | Oversight |
---

## Information Flow
```
Rules Definer creates formula
        │
        ├─→ Provides to Fenero: "stable := (y1-y2)/y2 ∈ [-0.05, +∞)"
        │   (Fenero executes this)
        │
        └─→ Provides to Deep Symbolic: formula + signature
            (Deep Symbolic verifies against this)
Data Source extracts data
        │
        ├─→ Provides to Fenero: {y1: 60000, y2: 50000}
        │   (Fenero computes on this)
        │
        └─→ Provides to Deep Symbolic: data + hash + signature
            (Deep Symbolic verifies matches)
Fenero executes in Secure On Prem
        │
        ├─ Apply formula to data
        ├─ Compute: (60000-50000)/50000 = 0.20
        ├─ Generate Z3 proof: "0.20 is in [-0.05, +∞)"
        │
        └─→ Provides to Deep Symbolic: only formula + output + proof + signature
            (Deep Symbolic now verifies)
            
Fenero Validator App powered by Deep Symbolic verifies for a Regulator/User/QC with "DATA"
        │
        ├─ Check 1: Fenero signature valid? ✅
        ├─ Check 2: Data hash matches? ✅
        ├─ Check 3: Formula signature valid? ✅
        ├─ Check 4: Z3 proof is sound? ✅
        │   (Proves that output is mathematically correct)
        │
        └─→ Issues Attestation: "Computation verified ✅"
            (Signed by Deep Symbolic)
Regulator audits
        │
        ├─ See attestation from Deep Symbolic ✅
        ├─ See Z3 proof (publicly verifiable)
        ├─ See all signatures (chain of custody)
        │
        └─ Conclusion: "Decision is auditable and correct"
```
---

## Who Knows What
```
                       RULES   DATA    COMPUTE   PROOF   SIGNATURES
Fenero                  ❌      ❌      ✅        ✅      ✅
  (executes)
  
Deep Symbolic           ❌      ❌      ❌        ✅      ✅
  (verifies)
  
Regulator               ❌      ❌      ❌        ✅      ✅
  (audits)
  
Rules Definer           ✅      ❌      ❌        ❌      ✅
  (creates)
  
Data Source             ❌      ✅      ❌        ❌      ✅
  (extracts)

Legend:
✅ = Sees/owns this
❌ = Doesn't see/own this
```
---

## What Each Actor Does
**Rules Definer:**

```
Input:  FNMA B3-3.1-01 (regulation)
Output: "stable := (y1-y2)/y2 ∈ [-0.05, +∞)"
        + signature (domain expert approval)
```
**Data Source:**

```
Input:  Documents (IRS 1040, W-2, etc.)
Output: {y1: 60000, y2: 50000}
        + hash (proof of what I extracted)
        + signature
```
**Fenero:**

```
Input:  Formula + Signed Data (both signed, not owned)
  Do:     Execute formula on signed data
Output: Result + Z3 proof + signature
        (doesn't own the rule or data, just executes)
```
**Deep Symbolic:**

```
Input:  Result + Proof + Signatures (all of above)
Do:     Verify mathematically using Z3
Output: Attestation (signed)
        (proves computation is correct)
```
**Regulator:**

```
Input:  Attestation + Z3 proof
Do:     Check signatures + verify proof
Output: "Decision is auditable ✅"
```
---

## Key Insights
### Fenero is NOT
- ❌ Rule owner (Rules Definer owns)
- ❌ Rule approver (Compliance owns)
- ❌ Data owner (Data Source owns)
- ❌ Data validator (Data Source Signs off on Fenero's work)
### Fenero IS
- ✅ Execution engine
- ✅ Proof generator
- ✅ Transparent (signs everything)
### Deep Symbolic Verifies
- ✅ Math is correct (Z3 proof)
- ✅ Signatures are valid
- ✅ Hashes match
- ❌ NOT why rule was created
- ❌ NOT how data was extracted
- ❌ NOT domain policy
### Regulator Trusts
- ✅ Deep Symbolic's attestation
- ✅ Z3 mathematical proof
- ✅ Signature chain
- ❌ NOT required to see rule content
- ❌ NOT required to see PII


