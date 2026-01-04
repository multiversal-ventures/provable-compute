# SDK Interface Specification

**Status:** Draft for Joint Review
**Last Updated:** 2026-01-04
**Package Name:** `provable-compute`

---

## Overview

The `provable-compute` SDK is a jointly developed library that converts computation results into verifiable formal proofs. It is designed to be:

- **Agnostic:** Works with Fenero's execution engine
- **Privacy-preserving:** Only hashes cross trust boundaries
- **Pluggable:** Supports multiple proof backends
- **Ontology-aware:** Supports MISMO, IRS Extended, and Employment ontologies

---

## Ontology System

The SDK works with Fenero's multi-layer ontology system for field extraction and validation:

| Ontology Type | Coverage | Document Types |
|---------------|----------|----------------|
| **MISMO 3.4** | Standard mortgage documents | W-2, 1040, standard forms |
| **IRS Extended** | Tax schedules & business returns | Schedule C, E, F, K-1, 1065, 1120, 1120S |
| **Employment** | Verification forms | VOE (Fannie Mae 1005, Freddie Mac 65) |

### Ontology Field Resolution

```python
# Each extraction field maps to a canonical ontology element
{
    "field_id": "schedule_c_depreciation",
    "canonical_name": "Line13_DepreciationAmount",  # Ontology element
    "aliases": ["line_13_depreciation", "depreciation"],  # Alternate names
    "ontology": "irs_schedule_c",
    "irs_line": "13"
}
```

The SDK validates that:
1. All input fields map to valid ontology elements
2. Canonical names are consistent across the proof
3. Ontology versions are recorded in the proof artifact

---

## Installation

```bash
# Python
pip install provable-compute

# Node.js (future)
npm install @multiversal/provable-compute
```

---

## Core API

### ProofGenerator

The main entry point for generating proofs.

```python
from provable_compute import ProofGenerator

class ProofGenerator:
    """
    Generate formal proofs from computation results.

    Joint SDK - Fenero + Deep Symbolic
    """

    def __init__(
        self,
        backend: str = "auto",
        signing_key: str | None = None,
        api_endpoint: str = "http://deepsymbolic-verifier.fenero.svc.cluster.local/v1"
    ):
        """
        Initialize the proof generator.

        Args:
            backend: Proof system - "z3", "lean", "coq", or "auto"
                     "auto" selects based on formula complexity
            signing_key: Path to private key for signing proofs
            api_endpoint: Deep Symbolic verification endpoint (in-cluster by default)
                          All verification happens on-premise - no data egress
        """
        ...

    def generate_proof(
        self,
        formulas: dict[str, str],
        inputs: dict[str, Any],
        outputs: dict[str, Any],
        metadata: ProofMetadata,
        sign: bool = True
    ) -> ProofArtifact:
        """
        Generate a formal proof from computation.

        Args:
            formulas: Named derivation formulas
                      {"pct_change": "(y1 - y2) / y2", "is_stable": "pct_change >= -0.05"}
            inputs: Input values used in computation
                    {"y1": 60000, "y2": 50000}
            outputs: Computation results
                     {"pct_change": 0.20, "is_stable": True, "outcome": "STABLE"}
            metadata: Identification and versioning info
            sign: Whether to sign the proof artifact

        Returns:
            ProofArtifact ready for verification

        Raises:
            ProofGenerationError: If proof cannot be generated
            UnsupportedExpressionError: If formula contains unsupported operations
        """
        ...

    def verify(
        self,
        artifact: ProofArtifact,
        timeout: float = 30.0
    ) -> VerificationResult:
        """
        Submit proof to Deep Symbolic for verification.

        Args:
            artifact: ProofArtifact from generate_proof()
            timeout: API timeout in seconds

        Returns:
            VerificationResult with attestation

        Raises:
            VerificationError: If verification fails
            APIError: If API call fails
        """
        ...

    async def verify_async(
        self,
        artifact: ProofArtifact
    ) -> VerificationResult:
        """Async version of verify()."""
        ...
```

---

### ProofArtifact

Output from proof generation, input to verification.

```python
from dataclasses import dataclass
from datetime import datetime

@dataclass
class ProofArtifact:
    """
    Proof artifact ready for verification.

    Contains hashes (not raw values) for privacy.
    """

    # Identification
    proof_id: str                  # UUID
    timestamp: datetime            # Generation time

    # Backend info
    backend: str                   # "z3" | "lean" | "coq"
    proof_format: str              # "smt2" | "lean4" | "gallina"

    # Hashes (privacy-preserving)
    inputs_hash: str               # SHA-256 of canonical input JSON
    formula_hash: str              # SHA-256 of canonical formula JSON
    result_hash: str               # SHA-256 of canonical output JSON

    # Proof content
    proof_content: bytes           # Backend-specific proof
    proof_size_bytes: int          # Size for monitoring

    # Metadata
    metadata: ProofMetadata        # Spec info, version, etc.

    # Signatures
    generator_signature: bytes | None  # SDK signature over artifact

    def to_verification_request(self) -> dict:
        """Format for Deep Symbolic Verification API."""
        return {
            "proof_id": self.proof_id,
            "timestamp": self.timestamp.isoformat(),
            "backend": self.backend,
            "proof_format": self.proof_format,
            "inputs_hash": self.inputs_hash,
            "formula_hash": self.formula_hash,
            "result_hash": self.result_hash,
            "proof_content": base64.b64encode(self.proof_content).decode(),
            "metadata": self.metadata.to_dict(),
            "generator_signature": base64.b64encode(self.generator_signature).decode()
                if self.generator_signature else None
        }

    def to_bytes(self) -> bytes:
        """Serialize for storage/transmission."""
        ...

    @classmethod
    def from_bytes(cls, data: bytes) -> "ProofArtifact":
        """Deserialize from storage/transmission."""
        ...
```

---

### ProofMetadata

Identification and context for proofs.

```python
@dataclass
class ProofMetadata:
    """Metadata identifying the computation being proved."""

    spec_name: str                 # e.g., "income_calculation"
    spec_version: str              # e.g., "2025.1.0"
    spec_hash: str | None = None   # Hash of spec definition

    # Ontology information
    ontologies: list[OntologyRef] = field(default_factory=list)

    # Optional context
    tenant_id: str | None = None   # Multi-tenant identifier
    case_id: str | None = None     # Business case reference
    execution_id: str | None = None # Trace ID

    # Custom fields
    extra: dict[str, str] = field(default_factory=dict)

    def to_dict(self) -> dict:
        ...


@dataclass
class OntologyRef:
    """Reference to an ontology used in extraction."""

    name: str                      # e.g., "irs_schedule_c", "mismo_3.4"
    version: str                   # e.g., "2025.12"
    document_types: list[str]      # e.g., ["IRSScheduleC"]
```

---

### ExtractionEvidence

Evidence of how input values were extracted from source documents.

```python
@dataclass
class ExtractionEvidence:
    """Evidence of data extraction for audit trail."""

    engine_version: str            # e.g., "fenero-underwriter-engine-v0.1"
    extracted_at: datetime

    sources: list[DocumentSource]
    inputs: list[ExtractedInput]


@dataclass
class DocumentSource:
    """Source document metadata."""

    document_id: str
    document_type: str             # e.g., "IRSScheduleC", "VerificationOfEmployment"
    ontology: str                  # e.g., "irs_schedule_c"
    document_hash: str             # SHA-256 of document
    tax_year: int | None = None
    page_count: int = 1


@dataclass
class ExtractedInput:
    """Individual extracted field with provenance."""

    field_id: str                  # Spec input identifier
    canonical_name: str            # Ontology element name (e.g., "Line13_DepreciationAmount")
    display_name: str              # Human-readable label

    value_hash: str                # SHA-256 of extracted value
    value_commitment: str | None   # Pedersen commitment for ZK
    data_type: str                 # "currency", "count", "date", etc.

    source: FieldLocation


@dataclass
class FieldLocation:
    """Location of extracted field in source document."""

    document_id: str
    ontology: str

    # Location info (varies by ontology type)
    irs_line: str | None = None              # IRS form line number
    box_label: str | None = None             # Form box label
    element_name: str | None = None          # Ontology element
    ontology_path: str | None = None         # MISMO path
    aliases: list[str] = field(default_factory=list)

    # Visual location
    coordinates: dict | None = None          # {"x", "y", "w", "h"}
    confidence: float = 1.0
```

---

### VerificationResult

Response from Deep Symbolic verification.

```python
@dataclass
class VerificationResult:
    """Result from Deep Symbolic verification."""

    verification_id: str           # Deep Symbolic's ID
    status: VerificationStatus     # VERIFIED | FAILED | ERROR

    # Detailed checks
    checks: VerificationChecks

    # Attestation (if verified)
    attestation: Attestation | None

    # Error info (if failed)
    error_code: str | None
    error_message: str | None


class VerificationStatus(Enum):
    VERIFIED = "VERIFIED"          # Proof is mathematically sound
    FAILED = "FAILED"              # Proof is invalid
    ERROR = "ERROR"                # Verification could not complete


@dataclass
class VerificationChecks:
    """Individual verification check results."""
    signature_valid: bool
    proof_sound: bool
    hashes_consistent: bool
    metadata_valid: bool


@dataclass
class Attestation:
    """Deep Symbolic's signed attestation."""
    statement: str                 # Human-readable statement
    signature: bytes               # Deep Symbolic's signature
    issued_at: datetime
    expires_at: datetime
    certificate_chain: list[str]   # For signature verification
```

---

## Expression Language

### Supported Expressions (P0 - Must Have)

| Expression | Example | Notes |
|------------|---------|-------|
| Addition | `a + b` | |
| Subtraction | `a - b` | |
| Multiplication | `a * b` | |
| Division | `a / b` | Division by zero handling TBD |
| Greater/Equal | `a >= b` | |
| Less/Equal | `a <= b` | |
| Greater | `a > b` | |
| Less | `a < b` | |
| Equality | `a == b` | |
| Not Equal | `a != b` | |
| Logical AND | `a && b` | |
| Logical OR | `a \|\| b` | |
| Logical NOT | `!a` | |
| Parentheses | `(a + b) * c` | |

### Supported Expressions (P1 - Should Have)

| Expression | Example | Notes |
|------------|---------|-------|
| Ternary | `a ? b : c` | |
| Max | `max(a, b)` | |
| Min | `min(a, b)` | |
| Absolute | `abs(a)` | |
| Round | `round(a, n)` | n decimal places |
| Floor | `floor(a)` | |
| Ceil | `ceil(a)` | |

### Future (P2)

- Array operations (`sum`, `avg`, `count`)
- Date arithmetic
- String operations
- Lookup tables

---

## Error Handling

```python
class ProvableComputeError(Exception):
    """Base exception for SDK errors."""
    pass

class ProofGenerationError(ProvableComputeError):
    """Proof could not be generated."""
    pass

class UnsupportedExpressionError(ProofGenerationError):
    """Formula contains unsupported expression."""
    expression: str
    suggestion: str | None

class VerificationError(ProvableComputeError):
    """Verification failed."""
    verification_id: str
    checks: VerificationChecks

class APIError(ProvableComputeError):
    """Deep Symbolic API error."""
    status_code: int
    response_body: str
```

---

## Usage Examples

### Basic Usage

```python
from provable_compute import ProofGenerator, ProofMetadata

# Initialize
gen = ProofGenerator(backend="z3")

# Define computation
formulas = {
    "pct_change": "(y1 - y2) / y2",
    "is_stable": "pct_change >= -0.05"
}
inputs = {"y1": 60000, "y2": 50000}
outputs = {"pct_change": 0.20, "is_stable": True}

# Generate proof
artifact = gen.generate_proof(
    formulas=formulas,
    inputs=inputs,
    outputs=outputs,
    metadata=ProofMetadata(
        spec_name="income_stability",
        spec_version="2025.1.0"
    )
)

# Verify
result = gen.verify(artifact)
print(result.status)  # VerificationStatus.VERIFIED
print(result.attestation.statement)  # "Computation mathematically verified"
```

### Async Background Processing

```python
from provable_compute import ProofGenerator, ProofMetadata
import asyncio

gen = ProofGenerator()

async def process_with_proof(computation_result):
    # Save result immediately (user sees it fast)
    await save_result(computation_result)

    # Generate and verify in background
    artifact = gen.generate_proof(
        formulas=computation_result.derivations,
        inputs=computation_result.inputs,
        outputs=computation_result.outputs,
        metadata=ProofMetadata(
            spec_name=computation_result.spec_name,
            spec_version=computation_result.spec_version,
            case_id=computation_result.case_id
        )
    )

    result = await gen.verify_async(artifact)
    await save_attestation(computation_result.id, result.attestation)
```

---

## Open Items

- [ ] Finalize expression language syntax (infix vs function style)
- [ ] Define division-by-zero behavior
- [ ] Determine array operation syntax
- [ ] Agree on error code taxonomy
- [ ] Define SDK versioning strategy
