{-# OPTIONS --safe #-}
open import zkir-v3.Assumptions

------------------------------------------------------------------------
-- Encoding of typed values to raw Fr  (ir_instructions/encode.rs)
--
-- `encode`/`decode` are the wire format crossing every circuit boundary
-- (inputs, transcripts, outputs, commitment).  They are *derived* from
-- the per-type trust-base primitives rather than assumed, keeping them
-- out of the trusted surface; only the primitives they call are trusted.
------------------------------------------------------------------------

module zkir-v3.Encoding (⋯ : _) (open Assumptions ⋯) where

open import zkir-v3.Types ⋯

open import Data.Bool    using (Bool; true; false)
open import Data.List    using (List; []; _∷_; length)
open import Data.Maybe   using (Maybe; just; nothing; map; _>>=_)
open import Data.Nat     using (ℕ; zero; suc; _≤_; s≤s; z≤n)
open import Data.Empty   using (⊥-elim)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_)
open import Data.Vec     using (Vec; []; _∷_; _++_; take; drop; head)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; trans; sym)
open import Relation.Nullary using (yes; no)

------------------------------------------------------------------------
-- Bool: one field element, 0 or 1  (AssignedBit::as_public_input /
-- from_public_input).
------------------------------------------------------------------------

bool→fr : Bool → Fr
bool→fr true  = 1ᶠ
bool→fr false = 0ᶠ

fr→bool : Fr → Maybe Bool
fr→bool x with x ≟ᶠ 0ᶠ
... | yes _ = just false
... | no  _ with x ≟ᶠ 1ᶠ
...   | yes _ = just true
...   | no  _ = nothing

------------------------------------------------------------------------
-- Bytes(n): one field element per chunk of the `Chunks` view (31
-- bytes, the last chunk shorter), each packed little-endian
-- (encode.rs: `encode_offcircuit` / `decode_bytes`).  A Byte is packed
-- as a 1-byte chunk.
------------------------------------------------------------------------

encode-chunks : ∀ {n} → Chunks n → Vec Byte n → List Fr
encode-chunks done       _  = []
encode-chunks (last _ _) bs = packᶠ bs ∷ []
encode-chunks (more c)   bs = packᶠ (take 31 bs) ∷ encode-chunks c (drop 31 bs)

decode-chunks : ∀ {n} → Chunks n → List Fr → Maybe (Vec Byte n)
decode-chunks done       []           = just []
decode-chunks done       (_ ∷ _)      = nothing
decode-chunks (last _ _) (x ∷ [])     = unpackᶠ _ x
decode-chunks (last _ _) _            = nothing
decode-chunks (more c)   (x ∷ xs)     =
  unpackᶠ 31 x        >>= λ h →
  decode-chunks c xs  >>= λ r →
  just (h ++ r)
decode-chunks (more c)   []           = nothing

encode-bytes : (n : ℕ) → Vec Byte n → List Fr
encode-bytes n = encode-chunks (chunks n)

decode-bytes : (n : ℕ) → List Fr → Maybe (Vec Byte n)
decode-bytes n = decode-chunks (chunks n)

-- At n = 32 this is still the (low, high) split of `Bytes32`.
_ : ∀ b → encode-bytes 32 b ≡ (let (lo , hi) = bytes32→low-high b in lo ∷ hi ∷ [])
_ = λ _ → refl

_ : ∀ lo hi → decode-bytes 32 (lo ∷ hi ∷ []) ≡ low-high→bytes32 lo hi
_ = λ _ _ → refl

------------------------------------------------------------------------
-- encode : flatten a typed value into raw field elements.
------------------------------------------------------------------------

encode : IrValue → List Fr
encode (val-native x)        = x ∷ []
encode (val-bool b)          = bool→fr b ∷ []
encode (val-byte b)          = packᶠ (b ∷ []) ∷ []
encode (val-bytes n bs)      = encode-bytes n bs
encode (val-jubjub-scalar s) = jubjubScalarToFr s ∷ []
encode (val-jubjub-point p)  = let (x , y)   = coordsJ p          in x  ∷ y  ∷ []
encode (val-secp256k1-base x)     = let (l , h) = secp256k1Base→limbs x   in l ∷ h ∷ []
encode (val-secp256k1-scalar s)   = let (l , h) = secp256k1Scalar→limbs s in l ∷ h ∷ []
encode (val-secp256k1-point p)    =
  let (a , b , c , d , e) = secp256k1Point→limbs p in a ∷ b ∷ c ∷ d ∷ e ∷ []
encode (val-secp256r1-base x)   =
  let (l , h) = secp256r1Base→limbs x   in l ∷ h ∷ []
encode (val-secp256r1-scalar s) =
  let (l , h) = secp256r1Scalar→limbs s in l ∷ h ∷ []
encode (val-secp256r1-point p)  =
  let (a , b , c , d , e) = secp256r1Point→limbs p in a ∷ b ∷ c ∷ d ∷ e ∷ []
encode (val-curve25519-base x)   =
  let (l , h) = curve25519Base→limbs x   in l ∷ h ∷ []
encode (val-curve25519-scalar s) =
  let (l , h) = curve25519Scalar→limbs s in l ∷ h ∷ []
encode (val-curve25519-point p)  =
  let (a , b , c , d) = curve25519Point→limbs p in a ∷ b ∷ c ∷ d ∷ []

------------------------------------------------------------------------
-- decode : read raw field elements as a value of the given type.
-- Partial: the wrong number of elements, or an invalid encoding (a
-- non-subgroup point, a non-canonical byte chunk/scalar, a field
-- element other than 0/1 for a Bool), yields `nothing`.
------------------------------------------------------------------------

decode : IrType → List Fr → Maybe IrValue
decode native        (x ∷ [])       = just (val-native x)
decode bool          (x ∷ [])       = map val-bool (fr→bool x)
decode byte          (x ∷ [])       = map (λ v → val-byte (head v)) (unpackᶠ 1 x)
decode (bytes⟨ n ⟩)     xs             = map (val-bytes n) (decode-bytes n xs)
decode jubjub-scalar (s ∷ [])       = map val-jubjub-scalar (jubjubScalarFromFr s)
decode jubjub-point  (x ∷ y ∷ [])   = map val-jubjub-point  (fromCoordsJ x y)
decode secp256k1-base     (l ∷ h ∷ [])   = map val-secp256k1-base     (limbs→secp256k1Base l h)
decode secp256k1-scalar   (l ∷ h ∷ [])   = map val-secp256k1-scalar   (limbs→secp256k1Scalar l h)
decode secp256k1-point    (a ∷ b ∷ c ∷ d ∷ e ∷ []) =
  map val-secp256k1-point (limbs→secp256k1Point a b c d e)
decode secp256r1-base   (l ∷ h ∷ []) =
  map val-secp256r1-base   (limbs→secp256r1Base l h)
decode secp256r1-scalar (l ∷ h ∷ []) =
  map val-secp256r1-scalar (limbs→secp256r1Scalar l h)
decode secp256r1-point  (a ∷ b ∷ c ∷ d ∷ e ∷ []) =
  map val-secp256r1-point (limbs→secp256r1Point a b c d e)
decode curve25519-base   (l ∷ h ∷ []) =
  map val-curve25519-base   (limbs→curve25519Base l h)
decode curve25519-scalar (l ∷ h ∷ []) =
  map val-curve25519-scalar (limbs→curve25519Scalar l h)
decode curve25519-point  (a ∷ b ∷ c ∷ d ∷ []) =
  map val-curve25519-point (limbs→curve25519Point a b c d)
decode _             _              = nothing

------------------------------------------------------------------------
-- Round-trip lemmas for the 3.1 encodings (Bool, Byte, Bytes(n)).
--
-- `*-round`: decode ∘ encode = id;  `*-sound`: encode ∘ decode = id on
-- the raw data decode accepts.  They follow from the packing laws
-- (`pack-round`, `pack-sound`) and `1ᶠ≢0ᶠ`; nothing new is assumed.
------------------------------------------------------------------------

bool-round : ∀ b → fr→bool (bool→fr b) ≡ just b
bool-round false with 0ᶠ ≟ᶠ 0ᶠ
... | yes _ = refl
... | no ¬p = ⊥-elim (¬p refl)
bool-round true with 1ᶠ ≟ᶠ 0ᶠ
... | yes p = ⊥-elim (1ᶠ≢0ᶠ p)
... | no  _ with 1ᶠ ≟ᶠ 1ᶠ
...   | yes _ = refl
...   | no ¬p = ⊥-elim (¬p refl)

bool-sound : ∀ {x b} → fr→bool x ≡ just b → bool→fr b ≡ x
bool-sound {x} eq with x ≟ᶠ 0ᶠ
bool-sound refl | yes x≡0 = sym x≡0
... | no _ with x ≟ᶠ 1ᶠ
bool-sound refl | no _ | yes x≡1 = sym x≡1

encode-chunks-len : ∀ {n} (c : Chunks n) bs
  → length (encode-chunks c bs) ≡ count c
encode-chunks-len done       _  = refl
encode-chunks-len (last _ _) _  = refl
encode-chunks-len (more c)   bs = cong suc (encode-chunks-len c (drop 31 bs))

chunks-round : ∀ {n} (c : Chunks n) bs
  → decode-chunks c (encode-chunks c bs) ≡ just bs
chunks-round done       []  = refl
chunks-round (last _ k≤31) bs = pack-round bs k≤31
chunks-round (more c)   bs
  rewrite pack-round (take 31 bs) ≤-refl
        | chunks-round c (drop 31 bs)
  = cong just (take++drop 31 bs)

chunks-sound : ∀ {n} (c : Chunks n) xs {bs}
  → decode-chunks c xs ≡ just bs → encode-chunks c bs ≡ xs
chunks-sound done       []           {[]} refl = refl
chunks-sound done       (_ ∷ _)      ()
chunks-sound (last _ _) []           ()
chunks-sound (last _ _) (x ∷ [])     eq = cong (_∷ []) (pack-sound eq)
chunks-sound (last _ _) (_ ∷ _ ∷ _)  ()
chunks-sound (more c)   []           ()
chunks-sound (more c)   (x ∷ xs)     eq
  with unpackᶠ 31 x in e₁ | decode-chunks c xs in e₂
chunks-sound (more c)   (x ∷ xs)     refl | just h | just r =
  cong₂ _∷_ (trans (cong packᶠ (take-++ 31 h r)) (pack-sound e₁))
            (trans (cong (encode-chunks c) (drop-++ 31 h r))
                   (chunks-sound c xs e₂))

bytes-len : ∀ n bs → length (encode-bytes n bs) ≡ nb-chunks n
bytes-len n = encode-chunks-len (chunks n)

bytes-round : ∀ n bs → decode-bytes n (encode-bytes n bs) ≡ just bs
bytes-round n = chunks-round (chunks n)

bytes-sound : ∀ n xs {bs} → decode-bytes n xs ≡ just bs → encode-bytes n bs ≡ xs
bytes-sound n = chunks-sound (chunks n)

byte-round : ∀ b → decode byte (encode (val-byte b)) ≡ just (val-byte b)
byte-round b rewrite pack-round (b ∷ []) (s≤s z≤n) = refl

byte-sound : ∀ {x v} → decode byte (x ∷ []) ≡ just v → encode v ≡ x ∷ []
byte-sound {x} eq with unpackᶠ 1 x in e
byte-sound refl | just (b ∷ []) = cong (_∷ []) (pack-sound e)
