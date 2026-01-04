# Security Model

**Status:** Draft for Joint Review
**Last Updated:** 2026-01-04

---

## Overview

This document defines the security model for the provable compute system, including:
- Trust boundaries
- Signature chain
- Key management
- Threat model

---

## Trust Model

### Actors and Trust Relationships

```
┌─────────────────────────────────────────────────────────────────┐
│                        TRUST BOUNDARY 1                         │
│                     (Fenero Environment)                        │
│                                                                 │
│  ┌─────────────┐    ┌─────────────┐    ┌─────────────────────┐ │
│  │ Rules       │    │ Data        │    │ Fenero              │ │
│  │ Definer     │    │ Source      │    │ Compute Engine      │ │
│  │             │    │             │    │                     │ │
│  │ Signs:      │    │ Signs:      │    │ Signs:              │ │
│  │ - Formula   │    │ - Data hash │    │ - Execution result  │ │
│  │ - Approval  │    │ - Extraction│    │ - Proof artifact    │ │
│  └─────────────┘    └─────────────┘    └─────────────────────┘ │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
                              │
                              │ ProofArtifact (hashes + signatures)
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│                        TRUST BOUNDARY 2                         │
│                   (Deep Symbolic Environment)                   │
│                                                                 │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │ Verification Service                                     │   │
│  │                                                          │   │
│  │ Verifies:                         Signs:                 │   │
│  │ - All upstream signatures         - Attestation          │   │
│  │ - Proof mathematical soundness    - Verification result  │   │
│  │ - Hash consistency                                       │   │
│  └─────────────────────────────────────────────────────────┘   │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
                              │
                              │ Attestation (signed)
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│                        TRUST BOUNDARY 3                         │
│                      (External Consumers)                       │
│                                                                 │
│  ┌─────────────┐    ┌─────────────┐    ┌─────────────────────┐ │
│  │ Validator   │    │ Regulator   │    │ Auditor             │ │
│  │ App         │    │             │    │                     │ │
│  │             │    │ Verifies:   │    │ Verifies:           │ │
│  │ Displays:   │    │ - DS sig    │    │ - Full chain        │ │
│  │ - Result    │    │ - Chain     │    │ - Compliance        │ │
│  │ - Attestation│   │             │    │                     │ │
│  └─────────────┘    └─────────────┘    └─────────────────────┘ │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

---

## Signature Chain

### Complete Chain of Custody

```
1. RULES DEFINER
   ├── Signs: Formula definition + version
   ├── Key: rules_definer_key
   └── Timestamp: When formula approved

2. DATA SOURCE
   ├── Signs: Extracted data hash + source reference
   ├── Key: data_source_key
   └── Timestamp: When data extracted

3. FENERO COMPUTATION
   ├── Signs: Input hash + output hash + derivation trace
   ├── Key: fenero_compute_key
   └── Timestamp: When computation executed

4. SDK PROOF GENERATION
   ├── Signs: ProofArtifact (proof content + all hashes)
   ├── Key: sdk_generator_key
   └── Timestamp: When proof generated

5. DEEP SYMBOLIC VERIFICATION
   ├── Signs: Attestation (verification result)
   ├── Key: deep_symbolic_key
   └── Timestamp: When verified
```

### Signature Payload Structures

#### Rules Definer Signature

```json
{
  "type": "formula_approval",
  "formula_hash": "sha256:...",
  "formula_version": "2025.1.0",
  "spec_name": "income_calculation",
  "approved_by": "compliance@customer.com",
  "approved_at": "2026-01-01T00:00:00Z"
}
```

#### Data Source Signature

```json
{
  "type": "data_extraction",
  "data_hash": "sha256:...",
  "source_documents": ["w2-2025.pdf", "1040-2025.pdf"],
  "extracted_by": "fenero-underwriter-engine-v0.1",
  "extracted_at": "2026-01-04T10:00:00Z"
}
```

#### Fenero Computation Signature

```json
{
  "type": "computation_result",
  "inputs_hash": "sha256:...",
  "formula_hash": "sha256:...",
  "outputs_hash": "sha256:...",
  "execution_id": "exec-abc-123",
  "computed_at": "2026-01-04T12:00:00Z"
}
```

#### SDK Generator Signature

```json
{
  "type": "proof_generation",
  "proof_id": "uuid",
  "proof_hash": "sha256:...",
  "backend": "z3",
  "inputs_hash": "sha256:...",
  "formula_hash": "sha256:...",
  "result_hash": "sha256:...",
  "generated_at": "2026-01-04T12:00:01Z"
}
```

#### Deep Symbolic Attestation Signature

```json
{
  "type": "verification_attestation",
  "verification_id": "ver-xyz",
  "proof_id": "uuid",
  "status": "VERIFIED",
  "checks_passed": ["signature", "proof_sound", "hashes"],
  "verified_at": "2026-01-04T12:00:05Z",
  "expires_at": "2027-01-04T12:00:05Z"
}
```

---

## Key Management

### Key Types

| Key | Owner | Purpose | Rotation |
|-----|-------|---------|----------|
| `rules_definer_key` | Customer | Sign formula approvals | Annual |
| `data_source_key` | Fenero | Sign data extractions | Annual |
| `fenero_compute_key` | Fenero | Sign computation results | Annual |
| `sdk_generator_key` | Joint (Fenero) | Sign proof artifacts | Annual |
| `deep_symbolic_key` | Deep Symbolic | Sign attestations | Annual |

### Key Infrastructure Options

#### Option A: PKI with CA (Recommended)

```
Root CA (Joint or Third-Party)
├── Fenero Intermediate CA
│   ├── fenero_compute_key
│   ├── data_source_key
│   └── sdk_generator_key
│
└── Deep Symbolic Intermediate CA
    └── deep_symbolic_key
```

**Pros:** Standard PKI, certificate chain verifiable
**Cons:** CA management overhead

#### Option B: Independent Key Pairs

Each party manages own keys, publish public keys out-of-band.

**Pros:** Simple, no CA dependency
**Cons:** Key distribution challenge, no revocation

#### Option C: HSM-Backed Keys

Keys stored in Hardware Security Modules.

**Pros:** Highest security
**Cons:** Cost, complexity

---

## Threat Model

### What We Protect Against

| Threat | Mitigation |
|--------|------------|
| **Tampered computation result** | Fenero signature on result |
| **Tampered proof** | SDK signature on proof artifact |
| **Fake attestation** | Deep Symbolic signature verification |
| **Replay attack** | Timestamps + proof_id uniqueness |
| **Man-in-the-middle** | TLS + signature verification |
| **Key compromise** | Key rotation, revocation lists |

### What We Do NOT Protect Against

| Threat | Why Not |
|--------|---------|
| **Incorrect formula** | Rules Definer responsibility |
| **Incorrect data extraction** | Data Source responsibility |
| **Bugs in Z3** | Trust Z3 (widely verified) |
| **Bugs in Deep Symbolic** | Trust Deep Symbolic implementation |

### Attack Scenarios

#### Scenario 1: Malicious Fenero Employee

**Attack:** Modify computation result before proof generation
**Detection:** Signature on result won't match if modified after signing
**Mitigation:** Verify Fenero signature before generating proof

#### Scenario 2: Compromised SDK

**Attack:** Generate fake proofs that verify
**Detection:** Deep Symbolic re-runs proof, would fail
**Mitigation:** Deep Symbolic independently verifies proof soundness

#### Scenario 3: Forged Attestation

**Attack:** Create fake attestation claiming verification passed
**Detection:** Deep Symbolic signature verification fails
**Mitigation:** Verifiers check Deep Symbolic certificate chain

---

## Privacy Guarantees

### Data That Leaves Fenero Environment

| Data | Leaves? | Format |
|------|---------|--------|
| PII (SSN, names) | NO | Never |
| Raw documents | NO | Never |
| Dollar amounts | NO | Hash only |
| Formula content | NO | Hash only |
| Computation result | NO | Hash only |
| Proof artifact | YES | Mathematical proof |
| Signatures | YES | Cryptographic signatures |
| Metadata (spec name, version) | YES | Plain text |

### Zero-Knowledge Properties

The system has **partial** zero-knowledge properties:

- Verifier learns: "computation is correct"
- Verifier does NOT learn: actual input values, formula details

**Note:** This is NOT a formal ZK-proof system. The proof reveals the structure of the computation but not the values.

---

## Compliance Considerations

### Audit Trail

Every verification produces an immutable record:
- Proof artifact (stored by Fenero)
- Verification result (stored by Deep Symbolic)
- Attestation (distributed to all parties)

### Data Residency

- Fenero: Customer data stays in customer-specified region
- Deep Symbolic: Only hashes + proofs, region TBD
- Attestations: Can be stored anywhere (no PII)

### Retention

| Data | Retention | Owner |
|------|-----------|-------|
| Raw documents | Per customer policy | Fenero |
| Computation results | Per customer policy | Fenero |
| Proof artifacts | TBD | Fenero |
| Verification records | TBD | Deep Symbolic |
| Attestations | TBD (suggest 7 years) | Both |

---

## Open Questions

- [ ] **Certificate Authority:** Joint CA, third-party, or independent keys?
- [ ] **HSM requirement:** Is HSM required for any keys?
- [ ] **Key rotation:** Automated or manual process?
- [ ] **Revocation:** How to handle compromised keys?
- [ ] **Audit logging:** What level of logging on verification API?
- [ ] **Data residency:** Where can Deep Symbolic store verification records?
