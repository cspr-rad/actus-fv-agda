open import Relation.Binary using (TotalOrder; DecTotalOrder)
import Relation.Binary.Definitions as B
open import Relation.Binary.Core using (Rel)
open import Data.Unit.Base
open import Data.Product using (_×_; _,_)
open import Data.Bool using (Bool; if_then_else_)
open import Data.Maybe.Base using (Maybe; nothing; just; maybe′; fromMaybe)
open import Data.List.Base hiding (fromMaybe)
open import Data.List.Sort
open import Data.Nat.Base hiding (_+_; _*_)
open import Data.Integer.Base as ℤ using (ℤ; +_; +0; +[1+_]; -[1+_])
open import Data.Rational.Base
open import Function.Base using (_∘_)
open import Agda.Builtin.Sigma
open import Relation.Nullary using (_because_; does)

module actus
  {a ℓ₁ ℓ₂} (O : DecTotalOrder a ℓ₁ ℓ₂)
  (yearFrac : DecTotalOrder.Carrier O → DecTotalOrder.Carrier O → ℚ)
  (observer : DecTotalOrder.Carrier O → ℤ)
  (CURS_Observer : DecTotalOrder.Carrier O → ℚ) where

open DecTotalOrder O renaming (Carrier to D)

-- Basic state machines with unfolding history formulated as a fold.
record MinskiMachine (i o s : Set) : Set where
  field
    state : s
    runMinskiMachine : s → i → o × s
open MinskiMachine

mmUpdate : ∀ {i o s} → MinskiMachine i o s → i → o × MinskiMachine i o s
mmUpdate mm i with mm .runMinskiMachine (mm .state) i
... | o , s = o , record { state = s; runMinskiMachine = mm .runMinskiMachine }

generateHistory : ∀ {i o s} → List i → MinskiMachine i o s → List o
generateHistory {i} {o} {s} = foldr rec (λ _ → []) where
  rec : i → (MinskiMachine i o s → List o) → MinskiMachine i o s → List o
  rec i r m with mmUpdate m i
  ... | o , m2 = o ∷ r m2


-- Sorted lists for schedules
-- data SortedList 
tag : ∀ {l1 l2 l3} → Set → TotalOrder l1 l2 l3 → TotalOrder l1 l2 l3
tag A record { Carrier = C ; _≈_ = e ; _≤_ = le ; isTotalOrder = record { isPartialOrder = record { isPreorder = record { isEquivalence = record { refl = refl ; sym = sym ; trans = trans₁ } ; reflexive = reflexive ; trans = trans } ; antisym = antisym } ; total = total } } =
  record { 
    Carrier = C × A;
    _≈_ = λ (c1 , _) (c2 , _) → e c1 c2; 
    _≤_ = λ (c1 , _) (c2 , _) → le c1 c2; 
    isTotalOrder = record { isPartialOrder = record { isPreorder = record { isEquivalence = record { refl = refl ; sym = sym ; trans = trans₁ } ; reflexive = reflexive ; trans = trans } ; antisym = antisym } ; total = λ (x , _) (y , _) → total x y }
  }

mergeList : ∀ {ℓ1 ℓ2} {A : Set ℓ1} {R : Rel A ℓ2} → B.Decidable R → List (List A) → List A
mergeList d = foldr (merge d) []



distTrans : ∀ {ℓ1 ℓ2} {d : Set ℓ1} {t : Set ℓ2} → List (List d × t) → List (List (d × t))
distTrans = map (λ (l , t) → map (λ d → (d , t)) l)

composeSchedules : ∀ {l} {t : Set l} → List (List D × t) → List (D × t)
composeSchedules = mergeList (λ (x , _) (y , _) → x ≤? y) ∘ distTrans



distEvent : ∀ {l1 l2 l3} {d : Set l1} {i : Set l2} {t : Set l3} → (i → t) → List (d × i) → List (d × t)
distEvent f = map (λ (d , i) → d , f i)

compileSchedules : ∀ {l1 l2} {t : Set l1} → List (Σ (Set l2) λ i → (i → t) × List (D × i)) → List (D × t)
compileSchedules = mergeList (λ (x , _) (y , _) → x ≤? y) ∘ map (λ(_ , (f , l)) → distEvent f l)












-- Machine which accepts transition function as input;
updateMachine : ∀ {i s o} → s → MinskiMachine (i × (i → s → o × s)) o s
updateMachine seed =
  record {
    state = seed;
    runMinskiMachine = λ s (i , t) → t i s
  }


-- Contract Performance
data PRF : Set where
  PRF_PF : PRF -- Performant
  PRF_DL : PRF -- Delayed
  PRF_DQ : PRF -- Delinquent
  PRF_DF : PRF -- Default

-- Contract State
record ContractState : Set a where
  field
    tmd   : Maybe D         -- Maturity Date (MD): The timestamp as per which the contract matures according to the initial terms or as per unscheduled events
    nt    : ℚ               -- Notional Principal (NT): The outstanding nominal value
    ipnr  : ℚ               -- Nominal Interest Rate (IPNR) : The applicable nominal rate
    ipac  : ℚ               -- Accrued Interest (IPAC): The current value of accrued interest
    ipac1 : Maybe ℚ         -- Accrued Interest (IPAC1): The current value of accrued interest of the first leg
    ipac2 : Maybe ℚ         -- Accrued Interest (IPAC2): The current value of accrued interest of the second leg
    ipla  : Maybe ℚ         -- Last Interst Period
    feac  : ℚ               -- Fee Accrued (FEAC): The current value of accrued fees
    nsc   : ℚ               -- Notional Scaling Multiplier (SCNT): The multiplier being applied to principal cash flows
    isc   : ℚ               -- InterestScalingMultiplier (SCIP): The multiplier being applied to interest cash flows
    prf   : PRF             -- Contract Performance (PRF)
    sd    : D               -- Status Date (MD): The timestamp as per which the state is captured at any point in time
    prnxt : ℚ               -- Next Principal Redemption Payment (PRNXT): The value at which principal is being repaid
    ipcb  : ℚ               -- Interest Calculation Base (IPCB)
    xd    : Maybe D         -- Exercise Date (XD)
    xa    : Maybe ℚ         -- Exercise Amount (XA)
open ContractState

data EventType : Set where
    IED  : EventType -- Initial Exchange
    FP   : EventType -- Fee Payment
    PR   : EventType -- Principal Redemption
    PD   : EventType -- Principal Drawing
    PY   : EventType -- Penalty Payment
    PP   : EventType -- Principal Prepayment (unscheduled event)
    IP   : EventType -- Interest Payment
    IPFX : EventType -- Interest Payment Fixed Leg
    IPFL : EventType -- Interest Payment Floating Leg
    IPCI : EventType -- Interest Capitalization
    CE   : EventType -- Credit Event
    RRF  : EventType -- Rate Reset Fixing with Known Rate
    RR   : EventType -- Rate Reset Fixing with Unknown Rate
    PRFX : EventType -- Principal Payment Amount Fixing
    DV   : EventType -- Dividend Payment
    PRD  : EventType -- Purchase
    MR   : EventType -- Margin Call
    TD   : EventType -- Termination
    SC   : EventType -- Scaling Index Fixing
    IPCB : EventType -- Interest Calculation Base Fixing
    MD   : EventType -- Maturity
    XD   : EventType -- Exercise
    STD  : EventType -- Settlement
    PI   : EventType -- Principal Increase
    AD   : EventType -- Monitoring

replace_tmd : Maybe D → ContractState → ContractState
replace_tmd d st = record st { tmd = d }

{- Most events calculate accumulated interest, Ipac. This is done by *adding* to Ipac
 * The fraction of the year since the last Sd,
 * times the last Ipnr, the Nominal Interest Rate
 * times the last Nt, the Notional Principal -}
updateInterest : D → ContractState → ContractState
updateInterest d st = record st { ipac = ipac st + (yearFrac (sd st) d * ipnr st * nt st); sd = d }


{- 
- t^AD, associated with the event AD.
  This is purely associated with Monitoring, and doesn't imply much of anything.
  This schedule is asserted by fiat and is not calculated automatically.
  When an AD event occures, 
  * accumulated interest is updated

  * there is no payoff/the payoff is 0
-}
PAM_AD_TRANS : D → ⊤ → ContractState → ContractState × ℚ
PAM_AD_TRANS d _ st = updateInterest d st , 0ℚ



{-
- t^IED, associated with the event IED, the Initial Exchange
  This is a singleton schedule; that is, it can only happen once.
  When this triggers, the contract, if it wasn't already setup, will be set up now.
  * Nt will be set to R(CNTRL) * NT
  * Ipnr will be 0 if INPR is undefined, otherwise it's set to INPR.
  * Ipac is set to IPAC if IPAC is defined;
    otherwise if IPANX is before the corrent time, Ipac is set to
    + the fraction of the year between IPANX and now
    + times the *new* Nt
    + times the *new* Ipnr
    otherwise Ipac is set to 0
    
  * The payout is 
    + The *observed* risk factor of CURS (whatever that is) at the current time
    + Times -R(CNTRL)
    + Times the sum NT and PDIED, the principal deposit at IED, determined as an input parameter.
-}
PAM_IED_TRANS : D → (ℚ × ℚ × Maybe ℚ × Maybe ℚ × Maybe D × ℚ) → ContractState → ContractState × ℚ
PAM_IED_TRANS d (NT , RCNTRL , INPR , IPAC , IPANX , PDIED) st = 
  let Nt' = RCNTRL * NT
      Ipnr' = fromMaybe 0ℚ INPR
      Ipac' = fromMaybe (maybe′ (λ IPANX → if does (IPANX ≤? d) then (yearFrac IPANX d * Nt' * Ipnr') else 0ℚ) 0ℚ IPANX) IPAC
  in record st { nt = Nt'; ipnr = Ipnr'; ipac = Ipac'; sd = d } , CURS_Observer d * (0ℚ - RCNTRL) * (NT + PDIED)




{-
- t^MD, associated with the event MD, the Maturity Date
  This is a singleton schedule; that is, it can only happen once.
  This nulls out many different values
  * Nt, Ipac, and Feac is set to 0
  
  * The payout is 
    + The *observed* risk factor of CURS (whatever that is) at the current time
    + Times the sum of
      ** Nsc * Nt
      ** Isc * Ipac
      ** Feac
-}
PAM_MD_TRANS : D → ⊤ → ContractState → ContractState × ℚ
PAM_MD_TRANS d _ st = 
  record st { nt = 0ℚ; ipac = 0ℚ; feac = 0ℚ } , 
  CURS_Observer d * ((nsc st + nt st) * (isc st + ipac st) * feac st)



{-
- t^PP, associated to the event PP, the Principal Prepayment
  If PPEF, the Principal Prepayment Effect, is N, that is, if there is No prepayment, then t^PP is empty.
  Otherwise, t^PP will inclode the *observed* PP events associated with CID (whatever that is), at the current time,
  along with a "cycle" of payments defined using the S-schedule function (see 3.1);
  * nothing, if OPANX, "cycle Anchor Date Of Optionality", and OPCL, the "cycle Of Optionality" are undefined.
  * IED + OPCL (what does "+" mean here?) if OPANX is undefined
  * OPANX
  call these "s", then the rest of t^PP is S(s, OPCL, T^MD) (How does T^MD differ from MD?)
-}
-- PAM_PP_TRANS : D → (Maybe ℚ × Maybe ℚ × ℚ) → ContractState → ContractState × ℚ
-- PAM_PP_TRANS d (OPANX , OPCL , IED) st = {!   !}


-- if (does (IPANX ≤? d)) then ? else ?