# Deep Symbolic Verification API

**Status:** Draft - Proposed Specification
**Last Updated:** 2026-01-04
**Owner:** Deep Symbolic (to be confirmed)

---

## Overview

This document specifies the Verification API that Deep Symbolic will provide. The API receives proof artifacts from the SDK and returns signed attestations.

> **Note:** This is Fenero's proposed specification. Deep Symbolic to confirm/modify.

---

## Deployment Requirement: On-Premise via Helm

**Critical:** This API must be deployable within Fenero's Kubernetes cluster. No data can leave the customer environment.

Deep Symbolic must provide:
- Docker container image (`deepsymbolic/verifier`)
- Helm chart for Kubernetes deployment
- Offline licensing (no call-home)
- Air-gapped operation support

See [01-architecture.md](01-architecture.md) for full deployment details.

---

## Base URL

When deployed on-premise via Helm:

```
In-Cluster:  http://deepsymbolic-verifier.fenero.svc.cluster.local/v1
```

For Deep Symbolic's own hosted environment (if applicable):

```
Production:  https://api.deepsymbolic.com/v1
Staging:     https://api.staging.deepsymbolic.com/v1
```

**Fenero will use the in-cluster endpoint.** Hosted endpoints are only for Deep Symbolic's other customers.

---

## Authentication

```
Authorization: Bearer <api_key>
```

API keys issued per-tenant by Deep Symbolic.

---

## Endpoints

### POST /verify

Verify a single proof artifact.

#### Request

```http
POST /api/v1/verify
Content-Type: application/json
Authorization: Bearer <api_key>

{
  "proof_id": "550e8400-e29b-41d4-a716-446655440000",
  "timestamp": "2026-01-04T12:00:00Z",

  "spec": {
    "name": "income_calculation",
    "version": "2025.1.0",
    "hash": "sha256:a1b2c3d4..."
  },

  "inputs_hash": "sha256:...",
  "result_hash": "sha256:...",
  "formula_hash": "sha256:...",

  "proof_content": "<base64-encoded-proof>",
  "proof_format": "smt2",
  "backend": "z3",

  "generator_signature": "<base64-encoded-signature>",

  "metadata": {
    "tenant_id": "fenero-prod",
    "case_id": "CASE-12345",
    "execution_id": "exec-abc-123"
  }
}
```

#### Response - Success (200)

```json
{
  "verification_id": "ver-789-xyz",
  "status": "VERIFIED",

  "checks": {
    "signature_valid": true,
    "proof_sound": true,
    "hashes_consistent": true,
    "metadata_valid": true
  },

  "attestation": {
    "statement": "Computation mathematically verified",
    "signature": "<base64:deep-symbolic-signature>",
    "issued_at": "2026-01-04T12:00:05Z",
    "expires_at": "2027-01-04T12:00:05Z",
    "certificate_chain": [
      "-----BEGIN CERTIFICATE-----\n...",
      "-----BEGIN CERTIFICATE-----\n..."
    ]
  },

  "timing": {
    "received_at": "2026-01-04T12:00:00.100Z",
    "verified_at": "2026-01-04T12:00:05.200Z",
    "duration_ms": 5100
  }
}
```

#### Response - Verification Failed (200)

```json
{
  "verification_id": "ver-789-xyz",
  "status": "FAILED",

  "checks": {
    "signature_valid": true,
    "proof_sound": false,
    "hashes_consistent": true,
    "metadata_valid": true
  },

  "attestation": null,

  "error": {
    "code": "PROOF_UNSOUND",
    "message": "Z3 returned UNSAT - proof does not hold",
    "details": {
      "solver_output": "...",
      "counterexample": "..."
    }
  }
}
```

#### Response - Error (4xx/5xx)

```json
{
  "error": {
    "code": "INVALID_SIGNATURE",
    "message": "Generator signature verification failed",
    "request_id": "req-abc-123"
  }
}
```

---

### GET /attestation/{verification_id}

Retrieve a previously issued attestation.

#### Request

```http
GET /api/v1/attestation/ver-789-xyz
Authorization: Bearer <api_key>
```

#### Response (200)

```json
{
  "verification_id": "ver-789-xyz",
  "status": "VERIFIED",
  "attestation": {
    "statement": "Computation mathematically verified",
    "signature": "<base64>",
    "issued_at": "2026-01-04T12:00:05Z",
    "expires_at": "2027-01-04T12:00:05Z"
  },
  "proof_id": "550e8400-e29b-41d4-a716-446655440000",
  "spec": {
    "name": "income_calculation",
    "version": "2025.1.0"
  }
}
```

---

### POST /verify/batch

Verify multiple proofs in a single request.

#### Request

```http
POST /api/v1/verify/batch
Content-Type: application/json
Authorization: Bearer <api_key>

{
  "proofs": [
    { /* same as single verify */ },
    { /* same as single verify */ },
    { /* same as single verify */ }
  ],
  "options": {
    "fail_fast": false,
    "parallel": true
  }
}
```

#### Response (200)

```json
{
  "batch_id": "batch-123",
  "results": [
    { "proof_id": "...", "status": "VERIFIED", "verification_id": "..." },
    { "proof_id": "...", "status": "VERIFIED", "verification_id": "..." },
    { "proof_id": "...", "status": "FAILED", "error": {...} }
  ],
  "summary": {
    "total": 3,
    "verified": 2,
    "failed": 1
  }
}
```

---

### GET /health

Health check endpoint.

```http
GET /api/v1/health
```

```json
{
  "status": "healthy",
  "version": "1.0.0",
  "backends": {
    "z3": "available",
    "lean": "available",
    "coq": "unavailable"
  }
}
```

---

## Error Codes

| Code | HTTP Status | Description |
|------|-------------|-------------|
| `INVALID_REQUEST` | 400 | Malformed request body |
| `INVALID_SIGNATURE` | 400 | Generator signature invalid |
| `UNSUPPORTED_BACKEND` | 400 | Requested backend not available |
| `UNSUPPORTED_FORMAT` | 400 | Proof format not recognized |
| `PROOF_TOO_LARGE` | 400 | Proof exceeds size limit |
| `PROOF_UNSOUND` | 200 | Proof verification failed (not an error) |
| `HASH_MISMATCH` | 200 | Hash verification failed |
| `UNAUTHORIZED` | 401 | Invalid or missing API key |
| `RATE_LIMITED` | 429 | Too many requests |
| `INTERNAL_ERROR` | 500 | Server error |
| `BACKEND_TIMEOUT` | 504 | Proof solver timed out |

---

## Rate Limits (TBD)

| Tier | Requests/min | Batch size | Proof size |
|------|--------------|------------|------------|
| Free | 10 | 5 | 100KB |
| Standard | 100 | 50 | 1MB |
| Enterprise | 1000 | 500 | 10MB |

---

## SLA Targets (TBD)

| Metric | Target |
|--------|--------|
| Availability | 99.9% |
| P50 latency | < 100ms |
| P99 latency | < 500ms |
| Proof timeout | 30s default, 5min max |

---

## Open Items (For Deep Symbolic)

### Deployment (Critical)

- [ ] **Confirm Helm chart delivery** - Can you provide a Helm chart for on-premise deployment?
- [ ] **Container registry** - Where will images be hosted? (Docker Hub, private registry, air-gapped delivery?)
- [ ] **Offline licensing** - How does licensing work without network access?
- [ ] **Air-gapped support** - Can the verifier run with zero egress?

### API Design

- [ ] Confirm API structure and endpoints
- [ ] Define authentication mechanism for in-cluster deployment (API key vs mTLS)
- [ ] Define attestation retention policy (local storage)

### Operational

- [ ] Resource requirements (CPU/memory) for Z3 verification workloads
- [ ] Horizontal scaling guidance (HPA configuration)
- [ ] Monitoring/metrics endpoints (Prometheus compatible?)
- [ ] Log format and verbosity configuration
