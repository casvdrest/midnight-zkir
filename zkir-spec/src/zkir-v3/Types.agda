{-# OPTIONS --safe #-}
open import zkir-v3.Assumptions

------------------------------------------------------------------------
-- Types and values of zkir-v3  (ir_types.rs)
--
-- The IR's type set, the off-circuit value domain `IrValue`, the
-- per-type encoding width, and the value→type and default-value maps.
------------------------------------------------------------------------

module zkir-v3.Types (⋯ : _) (open Assumptions ⋯) where

open import Data.Bool using (Bool)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _≤?_; s≤s; z≤n)
open import Data.Nat.Properties using (≤∧≢⇒<) renaming (_≟_ to _≟ℕ_)
open import Data.Product using (_×_; _,_)
open import Data.Product.Properties using (≡-dec)
open import Data.Sum using (_⊎_)
open import Data.Vec using (Vec)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Relation.Nullary using (yes; no; Dec)
open import Relation.Nullary.Decidable using (map′; _×-dec_)
open import Data.Unit using (⊤; tt)

------------------------------------------------------------------------
-- Types  (ir_types.rs: IrType)
--
-- ZKIR 3.1 has fifteen types.  `bool` and `byte` are new in 3.1, and
-- `bytes⟨ n ⟩` generalizes the 3.0 type `Bytes32`, which is `bytes⟨ 32 ⟩`
-- (kept available as the pattern synonym `bytes32`).  The constructor
-- order follows the Rust enum, not its binary discriminants.
------------------------------------------------------------------------

data IrType : Set where
  native            : IrType   -- Scalar<BLS12-381>
  bool              : IrType   -- Bool          (3.1)
  byte              : IrType   -- Byte          (3.1)
  bytes⟨_⟩          : ℕ → IrType   -- Bytes<n>  (3.1; Bytes<32> in 3.0)
  jubjub-point      : IrType   -- Point<Jubjub>
  jubjub-scalar     : IrType   -- Scalar<Jubjub>
  secp256k1-point        : IrType   -- Point<Secp256k1>
  secp256k1-base         : IrType   -- Base<Secp256k1>
  secp256k1-scalar       : IrType   -- Scalar<Secp256k1>
  secp256r1-point   : IrType   -- Point<Secp256r1>
  secp256r1-base    : IrType   -- Base<Secp256r1>
  secp256r1-scalar  : IrType   -- Scalar<Secp256r1>
  curve25519-point  : IrType   -- Point<Curve25519>
  curve25519-base   : IrType   -- Base<Curve25519>
  curve25519-scalar : IrType   -- Scalar<Curve25519>

-- The ZKIR 3.0 type `Bytes<32>`.
--
-- 32 is spelled in constructor form: Agda refuses to match on a numeric
-- literal above 20 when it has to expand it for unification (here, the
-- length index of `val-bytes`), and the constructor form sidesteps that.
-- It is definitionally equal to the literal 32.
pattern ‵32 = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (zero))))))))))))))))))))))))))))))))
pattern bytes32 = bytes⟨ ‵32 ⟩

------------------------------------------------------------------------
-- Valid types.
--
-- The Rust parsers (JSON and binary) only produce `Bytes<n>` with
-- 1 ≤ n ≤ MAX_BYTES_LEN = 2²⁴, so no source can mention another length.
-- The model keeps `bytes⟨_⟩` total over ℕ and states the bound as a
-- decidable predicate instead.  (Not yet part of the producer
-- obligations: nothing downstream depends on it so far.)
------------------------------------------------------------------------

MAX-BYTES-LEN : ℕ
MAX-BYTES-LEN = 16777216   -- 2²⁴ (ir_types.rs: MAX_BYTES_LEN)

ValidType : IrType → Set
ValidType (bytes⟨ n ⟩) = 1 ≤ n × n ≤ MAX-BYTES-LEN
ValidType _         = ⊤

valid-type? : ∀ t → Dec (ValidType t)
valid-type? native            = yes tt
valid-type? bool              = yes tt
valid-type? byte              = yes tt
valid-type? (bytes⟨ n ⟩)         = (1 ≤? n) ×-dec (n ≤? MAX-BYTES-LEN)
valid-type? jubjub-point      = yes tt
valid-type? jubjub-scalar     = yes tt
valid-type? secp256k1-point   = yes tt
valid-type? secp256k1-base    = yes tt
valid-type? secp256k1-scalar  = yes tt
valid-type? secp256r1-point   = yes tt
valid-type? secp256r1-base    = yes tt
valid-type? secp256r1-scalar  = yes tt
valid-type? curve25519-point  = yes tt
valid-type? curve25519-base   = yes tt
valid-type? curve25519-scalar = yes tt

------------------------------------------------------------------------
-- Encoding widths  (ir_types.rs: IrType::encoded_len)
------------------------------------------------------------------------

-- The chunking of an n-byte string into BYTES-PER-FR-byte chunks, the
-- last one shorter (ir_instructions/encode.rs: `bs.chunks(31)`), as a
-- view on n.  `chunks n` computes it; for a closed n it normalizes to a
-- closed view (e.g. `chunks 32 = more (last _ _)`, 31 bytes then 1), so
-- the encoding of a `Bytes32` still computes to two field elements.
data Chunks : ℕ → Set where
  done : Chunks 0
  last : ∀ {n} → 1 ≤ n → n ≤ BYTES-PER-FR → Chunks n
  more : ∀ {n} → Chunks (suc n) → Chunks (BYTES-PER-FR + suc n)

private
  -- Chunks of n + 1 bytes, from the chunks of n bytes: append a byte to
  -- the last chunk, opening a new one when it is full.
  step : ∀ {n} → Chunks n → Chunks (suc n)
  step done = last (s≤s z≤n) (s≤s z≤n)
  step (last {n} _ n≤31) with n ≟ℕ BYTES-PER-FR
  ... | yes refl = more (last (s≤s z≤n) (s≤s z≤n))
  ... | no  n≢31 = last (s≤s z≤n) (≤∧≢⇒< n≤31 n≢31)
  step (more c) = more (step c)

chunks : ∀ n → Chunks n
chunks zero    = done
chunks (suc n) = step (chunks n)

-- Number of chunks: ⌈n / 31⌉ (ir_types.rs:
-- `n.div_ceil(BYTES_PER_FIELD_ELEMENT)`).
count : ∀ {n} → Chunks n → ℕ
count done       = 0
count (last _ _) = 1
count (more c)   = suc (count c)

nb-chunks : ℕ → ℕ
nb-chunks n = count (chunks n)

-- Number of raw Fr elements needed to encode a value of this type.
encoded-len : IrType → ℕ
encoded-len native            = 1
encoded-len bool              = 1
encoded-len byte              = 1
encoded-len (bytes⟨ n ⟩)         = nb-chunks n
encoded-len jubjub-point      = 2
encoded-len jubjub-scalar     = 1
encoded-len secp256k1-point        = 5
encoded-len secp256k1-base         = 2
encoded-len secp256k1-scalar       = 2
encoded-len secp256r1-point   = 5
encoded-len secp256r1-base    = 2
encoded-len secp256r1-scalar  = 2
encoded-len curve25519-point  = 4
encoded-len curve25519-base   = 2
encoded-len curve25519-scalar = 2

-- Bytes32 still takes two elements: 31 bytes, then 1.
_ : encoded-len bytes32 ≡ 2
_ = refl

_ : nb-chunks 0 ≡ 0 × nb-chunks 31 ≡ 1 × nb-chunks 62 ≡ 2 × nb-chunks 63 ≡ 3
_ = refl , refl , refl , refl

------------------------------------------------------------------------
-- Off-circuit values  (ir_types.rs: IrValue)
--
-- Constructors carry the concrete carrier; they are named distinctly
-- from the `IrType` tags to avoid overloading.  A `val-bytes` value carries
-- its length, as the Rust `Vec<u8>` does at run time.
------------------------------------------------------------------------

data IrValue : Set where
  val-native            : Fr               → IrValue
  val-bool              : Bool             → IrValue
  val-byte              : Byte             → IrValue
  val-bytes             : (n : ℕ) → Vec Byte n → IrValue
  val-jubjub-point      : JubjubPoint      → IrValue
  val-jubjub-scalar     : JubjubScalar     → IrValue
  val-secp256k1-point        : Secp256k1Point        → IrValue
  val-secp256k1-base         : Secp256k1Base         → IrValue
  val-secp256k1-scalar       : Secp256k1Scalar       → IrValue
  val-secp256r1-point   : Secp256r1Point   → IrValue
  val-secp256r1-base    : Secp256r1Base    → IrValue
  val-secp256r1-scalar  : Secp256r1Scalar  → IrValue
  val-curve25519-point  : Curve25519Point  → IrValue
  val-curve25519-base   : Curve25519Base   → IrValue
  val-curve25519-scalar : Curve25519Scalar → IrValue

-- A ZKIR 3.0 `Bytes32` value.
pattern val-bytes32 b = val-bytes ‵32 b

-- The type of a value  (ir_types.rs: IrValue::get_type).
typeof : IrValue → IrType
typeof (val-native            _) = native
typeof (val-bool              _) = bool
typeof (val-byte              _) = byte
typeof (val-bytes           n _) = bytes⟨ n ⟩
typeof (val-jubjub-point      _) = jubjub-point
typeof (val-jubjub-scalar     _) = jubjub-scalar
typeof (val-secp256k1-point        _) = secp256k1-point
typeof (val-secp256k1-base         _) = secp256k1-base
typeof (val-secp256k1-scalar       _) = secp256k1-scalar
typeof (val-secp256r1-point   _) = secp256r1-point
typeof (val-secp256r1-base    _) = secp256r1-base
typeof (val-secp256r1-scalar  _) = secp256r1-scalar
typeof (val-curve25519-point  _) = curve25519-point
typeof (val-curve25519-base   _) = curve25519-base
typeof (val-curve25519-scalar _) = curve25519-scalar

------------------------------------------------------------------------
-- Decidable equality of types (used by the type checks of `cond-select`
-- and the `output` terminator).
--
-- Decided through an injective code into ℕ × ℕ (constructor index,
-- byte length), so the table does not grow quadratically with the
-- number of types.  On closed types it still computes to `yes refl` /
-- `no _`.
------------------------------------------------------------------------

private
  code : IrType → ℕ × ℕ
  code native            = 0  , 0
  code bool              = 1  , 0
  code byte              = 2  , 0
  code (bytes⟨ n ⟩)         = 3  , n
  code jubjub-point      = 4  , 0
  code jubjub-scalar     = 5  , 0
  code secp256k1-point   = 6  , 0
  code secp256k1-base    = 7  , 0
  code secp256k1-scalar  = 8  , 0
  code secp256r1-point   = 9  , 0
  code secp256r1-base    = 10 , 0
  code secp256r1-scalar  = 11 , 0
  code curve25519-point  = 12 , 0
  code curve25519-base   = 13 , 0
  code curve25519-scalar = 14 , 0

  uncode : ℕ × ℕ → Maybe IrType
  uncode (0  , _) = just native
  uncode (1  , _) = just bool
  uncode (2  , _) = just byte
  uncode (3  , n) = just (bytes⟨ n ⟩)
  uncode (4  , _) = just jubjub-point
  uncode (5  , _) = just jubjub-scalar
  uncode (6  , _) = just secp256k1-point
  uncode (7  , _) = just secp256k1-base
  uncode (8  , _) = just secp256k1-scalar
  uncode (9  , _) = just secp256r1-point
  uncode (10 , _) = just secp256r1-base
  uncode (11 , _) = just secp256r1-scalar
  uncode (12 , _) = just curve25519-point
  uncode (13 , _) = just curve25519-base
  uncode (14 , _) = just curve25519-scalar
  uncode _        = nothing

  uncode-code : ∀ t → uncode (code t) ≡ just t
  uncode-code native            = refl
  uncode-code bool              = refl
  uncode-code byte              = refl
  uncode-code (bytes⟨ n ⟩)         = refl
  uncode-code jubjub-point      = refl
  uncode-code jubjub-scalar     = refl
  uncode-code secp256k1-point   = refl
  uncode-code secp256k1-base    = refl
  uncode-code secp256k1-scalar  = refl
  uncode-code secp256r1-point   = refl
  uncode-code secp256r1-base    = refl
  uncode-code secp256r1-scalar  = refl
  uncode-code curve25519-point  = refl
  uncode-code curve25519-base   = refl
  uncode-code curve25519-scalar = refl

  code-injective : ∀ {t u} → code t ≡ code u → t ≡ u
  code-injective {t} {u} eq =
    just-injective (trans (sym (uncode-code t))
                          (trans (cong uncode eq) (uncode-code u)))

_≟T_ : DecidableEquality IrType
t ≟T u = map′ code-injective (cong code) (≡-dec _≟ℕ_ _≟ℕ_ (code t) (code u))

------------------------------------------------------------------------
-- The elliptic-curve families that `ec-mul-generator`,
-- `into-coordinates` and `from-coordinates` dispatch on.
--
-- Each of those three instructions picks a curve from an operand's type
-- and produces a result in a matching type of the same curve.
-- `ECFamily` names the curve; the columns give its point type, the type
-- of a point's x/y coordinates, its scalar type, the carriers behind the
-- point and coordinate types, and the `IrValue` constructors injecting
-- those carriers.  The recognizers invert the type columns, reading the
-- family off an operand's type.  So the point ↔ coordinate ↔ scalar
-- pairing lives in one table instead of being re-derived at each
-- dispatch site.
--
-- `ec-families` is the dispatch table of `into-coordinates` and
-- `from-coordinates`.  `ec-mul-generator` uses `gen-families`, which the
-- Rust supports only for Jubjub and Secp256k1.
------------------------------------------------------------------------

data ECFamily : Set where
  jubjub secp256k1 secp256r1 curve25519 : ECFamily

pointTy : ECFamily → IrType
pointTy jubjub     = jubjub-point
pointTy secp256k1  = secp256k1-point
pointTy secp256r1  = secp256r1-point
pointTy curve25519 = curve25519-point

coordTy : ECFamily → IrType
coordTy jubjub     = native
coordTy secp256k1  = secp256k1-base
coordTy secp256r1  = secp256r1-base
coordTy curve25519 = curve25519-base

scalarTy : ECFamily → IrType
scalarTy jubjub     = jubjub-scalar
scalarTy secp256k1  = secp256k1-scalar
scalarTy secp256r1  = secp256r1-scalar
scalarTy curve25519 = curve25519-scalar

Pointᶠ : ECFamily → Set
Pointᶠ jubjub     = JubjubPoint
Pointᶠ secp256k1  = Secp256k1Point
Pointᶠ secp256r1  = Secp256r1Point
Pointᶠ curve25519 = Curve25519Point

-- Jubjub's coordinates are plain `Fr`: on the Edwards model its base
-- field is the circuit's own field, which is why `coordTy jubjub` is
-- `native` rather than a curve-specific base type.
Coordᶠ : ECFamily → Set
Coordᶠ jubjub     = Fr
Coordᶠ secp256k1  = Secp256k1Base
Coordᶠ secp256r1  = Secp256r1Base
Coordᶠ curve25519 = Curve25519Base

val-pointᶠ : ∀ f → Pointᶠ f → IrValue
val-pointᶠ jubjub     = val-jubjub-point
val-pointᶠ secp256k1  = val-secp256k1-point
val-pointᶠ secp256r1  = val-secp256r1-point
val-pointᶠ curve25519 = val-curve25519-point

val-coordᶠ : ∀ f → Coordᶠ f → IrValue
val-coordᶠ jubjub     = val-native
val-coordᶠ secp256k1  = val-secp256k1-base
val-coordᶠ secp256r1  = val-secp256r1-base
val-coordᶠ curve25519 = val-curve25519-base

pointFamily : IrType → Maybe ECFamily
pointFamily jubjub-point     = just jubjub
pointFamily secp256k1-point  = just secp256k1
pointFamily secp256r1-point  = just secp256r1
pointFamily curve25519-point = just curve25519
pointFamily _                = nothing

coordFamily : IrType → Maybe ECFamily
coordFamily native          = just jubjub
coordFamily secp256k1-base  = just secp256k1
coordFamily secp256r1-base  = just secp256r1
coordFamily curve25519-base = just curve25519
coordFamily _               = nothing

-- Jubjub and Secp256k1 only: `EcMulGenerator` is not extended to the
-- other two curves, so their scalars fall to the catch-all.
genScalarFamily : IrType → Maybe ECFamily
genScalarFamily jubjub-scalar    = just jubjub
genScalarFamily secp256k1-scalar = just secp256k1
genScalarFamily _                = nothing

-- Every recognizer inverts its type column, and every value column
-- lands in the type column it is paired with.
_ : ∀ f → pointFamily (pointTy f) ≡ just f
        × coordFamily (coordTy f) ≡ just f
        × (∀ p → typeof (val-pointᶠ f p) ≡ pointTy f)
        × (∀ x → typeof (val-coordᶠ f x) ≡ coordTy f)
_ = λ { jubjub     → refl , refl , (λ _ → refl) , (λ _ → refl)
      ; secp256k1  → refl , refl , (λ _ → refl) , (λ _ → refl)
      ; secp256r1  → refl , refl , (λ _ → refl) , (λ _ → refl)
      ; curve25519 → refl , refl , (λ _ → refl) , (λ _ → refl) }

ec-families : List ECFamily
ec-families = jubjub ∷ secp256k1 ∷ secp256r1 ∷ curve25519 ∷ []

gen-families : List ECFamily
gen-families = jubjub ∷ secp256k1 ∷ []

-- "`P` holds of one of `fs`", laid out as the right-nested `⊎` that the
-- dispatching instructions' per-family disjuncts are consumed as.
Anyᶠ : (ECFamily → Set) → List ECFamily → Set
Anyᶠ P []           = ⊥
Anyᶠ P (f ∷ [])     = P f
Anyᶠ P (f ∷ g ∷ fs) = P f ⊎ Anyᶠ P (g ∷ fs)
