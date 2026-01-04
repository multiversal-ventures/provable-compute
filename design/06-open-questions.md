# Open Questions & Meeting Agenda

**Status:** Meeting Preparation
**Last Updated:** 2026-01-04
**Purpose:** First joint meeting between Fenero and Deep Symbolic

---

## Meeting Objectives

1. **Alignment:** Confirm shared understanding of the system
2. **Decisions:** Make key technical decisions to unblock development
3. **Ownership:** Clarify who builds what
4. **Next Steps:** Define PoC scope and timeline

---

## Priority 1: Must Decide in First Meeting

### 1.1 Proof System Selection

**Question:** Which proof backend do we start with?

| Option | Fenero Position | For Deep Symbolic |
|--------|-----------------|-------------------|
| **Z3 (Recommended)** | Covers our P0 needs, fast, simple | What's your experience with Z3? |
| Lean 4 | Future option | Do you have Lean expertise? |
| Coq | Overkill for now | Any customer requirements for Coq? |

**Fenero Recommendation:** Start with Z3, evaluate Lean for Phase 2

**Decision needed:** [ ] Confirmed Z3 for Phase 1

---

### 1.2 SDK Ownership Model

**Question:** How do we split development work?

**Proposed Split:**

| Component | Owner | Rationale |
|-----------|-------|-----------|
| Expression parser/AST | Fenero | We know our formula syntax |
| Formula normalization | Fenero | Domain knowledge |
| SMT-LIB2 translation | Joint | Shared responsibility |
| Proof optimization | Deep Symbolic | Your expertise |
| Signature generation | Deep Symbolic | Your security expertise |
| Verification client | Joint | Both need to use it |

**Decision needed:** [ ] Ownership confirmed

---

### 1.3 Repository & Licensing

**Question:** Where does the code live?

| Option | Pros | Cons |
|--------|------|------|
| Joint GitHub org | Clean separation | New org to manage |
| Fenero org, DS maintainers | Simple | Perception |
| DS org, Fenero maintainers | Simple | Perception |

**Fenero Proposal:**
- Repo: `github.com/multiversal-ventures/provable-compute` (or joint org)
- License: MIT

**Decision needed:** [ ] Repo location and license

---

### 1.4 Verification API Deployment (CRITICAL)

**Requirement:** The Verification API must be deployable on-premise within Fenero's Kubernetes cluster via Helm.

**Rationale:** No data can leave Fenero's environment. Customer data, proofs, and attestations must all stay within the secure boundary.

**Deep Symbolic must provide:**

| Deliverable | Description |
|-------------|-------------|
| Docker image | `deepsymbolic/verifier` container |
| Helm chart | `charts/deepsymbolic-verifier` |
| Offline licensing | No call-home, air-gapped capable |
| Documentation | Deployment guide, resource sizing |

**Questions for Deep Symbolic:**
- [ ] Can you deliver a Helm chart for on-premise deployment?
- [ ] What's your licensing model for on-premise? (per-node, per-verification, annual?)
- [ ] Container registry: Docker Hub, private, or air-gapped tarball delivery?
- [ ] Resource requirements: CPU/memory for Z3 workloads?
- [ ] Do you have existing customers running on-premise?

---

## Priority 2: Should Decide Soon

### 2.1 Authentication & API Access

**Question:** How does Fenero authenticate to Deep Symbolic API?

| Option | Complexity | Security |
|--------|------------|----------|
| API Keys | Low | Medium |
| OAuth 2.0 / OIDC | Medium | High |
| Mutual TLS | High | Very High |

**Fenero Preference:** Start with API keys, upgrade later if needed

---

### 2.2 Key Management

**Question:** How do we manage signing keys?

**Sub-questions:**
- Who issues SDK signing certificates?
- Certificate Authority: Joint, third-party, or independent?
- HSM requirements?
- Key rotation process?

**Fenero Position:** Open to discussion, prefer simplicity for PoC

---

### 2.3 Pricing Model (On-Premise)

**Question:** How will on-premise deployment be priced?

| Model | Description |
|-------|-------------|
| Per-node | Annual fee per K8s node running verifier |
| Per-verification | Metered usage (requires call-home or audit) |
| Flat annual | Unlimited verifications for annual fee |
| Per-customer | Fenero pays per end-customer deployment |

**Fenero Position:** Prefer flat annual or per-customer to simplify our pricing model. Need call-home-free licensing.

---

### 2.4 Data Retention

**Question:** How long does Deep Symbolic store verification records?

**Considerations:**
- Audit requirements (7+ years for financial)
- Storage costs
- GDPR/privacy implications (though we only send hashes)

---

## Priority 3: Can Decide Later

### 3.1 Batch Verification

- Batch API implementation timeline?
- Max batch size?
- Async webhook support?

### 3.2 Advanced Backends

- When would we add Lean 4?
- Customer demand for Coq?

### 3.3 SDK Distribution

- PyPI package name?
- npm package (do we need JS/TS)?
- Versioning strategy?

### 3.4 Validator App

- Fenero builds this, correct?
- Any Deep Symbolic branding requirements?
- Whitelabel options?

---

## Technical Questions for Deep Symbolic

### Z3 Specifics

1. What Z3 version do you run in production?
2. Any Z3 configurations/optimizations you recommend?
3. Timeout handling - what happens if Z3 doesn't terminate?
4. Have you verified proofs from external Z3 generators before?

### API Design

5. Review of proposed API spec (doc 03) - feedback?
6. Any existing API patterns we should align with?
7. Webhook support for async verification?

### Security

8. How do you handle key/certificate provisioning?
9. Do you have SOC 2 / ISO 27001?
10. Penetration testing on verification API?

---

## Proposed PoC Scope

### Goal
End-to-end proof generation and verification for simple arithmetic

### Spec
```
Income Stability Calculation
- Inputs: y1 (current year income), y2 (prior year income)
- Formula: pct_change = (y1 - y2) / y2
- Condition: is_stable = pct_change >= -0.05
- Output: STABLE or UNSTABLE
```

### Deliverables

| # | Deliverable | Owner |
|---|-------------|-------|
| 1 | Expression parser for arithmetic | Fenero |
| 2 | Z3 SMT-LIB2 generator | Joint |
| 3 | ProofArtifact serialization | Joint |
| 4 | Verification API endpoint | Deep Symbolic |
| 5 | End-to-end integration test | Joint |

### Success Criteria

- [ ] Generate Z3 proof from sample calculation
- [ ] Submit proof to Deep Symbolic API
- [ ] Receive signed attestation
- [ ] Verify attestation signature

---

## Action Items Template

| # | Action | Owner | Due |
|---|--------|-------|-----|
| 1 | | | |
| 2 | | | |
| 3 | | | |

---

## Notes

*(To be filled during meeting)*
