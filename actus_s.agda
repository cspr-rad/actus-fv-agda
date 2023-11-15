open import Relation.Binary using (TotalOrder; DecTotalOrder)
import Relation.Binary.Definitions as B
open import Relation.Binary.Core using (Rel)
open import Data.Unit.Base
open import Data.Product using (_×_; _,_)
open import Data.Bool using (Bool; if_then_else_; _∨_; _∧_; not)
open import Data.Maybe.Base using (Maybe; nothing; just; maybe′; fromMaybe)
open import Data.List.Base hiding (fromMaybe; concat)
open import Data.List.Sort
open import Data.Nat.Base hiding (_+_; _*_; _≤ᵇ_)
open import Data.Integer.Base as ℤ using (ℤ; +_; +0; +[1+_]; -[1+_])
open import Data.Rational.Base
open import Data.Rational.Unnormalised.Base using (_≢0)
open import Data.String hiding (head; _≟_)
open import Data.String.Base using (concat)
open import Function.Base using (_∘_)
open import Agda.Builtin.Sigma
open import Relation.Nullary using (_because_; does; Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; _≢_; cong)

module actus_s
  {a ℓ₁ ℓ₂} (O : DecTotalOrder a ℓ₁ ℓ₂) (_+D_ : DecTotalOrder.Carrier O → DecTotalOrder.Carrier O → DecTotalOrder.Carrier O)
  (yearFrac : DecTotalOrder.Carrier O → DecTotalOrder.Carrier O → ℚ)
  (yearDist : ∀ a b → a ≢ b → ℤ.∣ ↥ yearFrac a b ∣ ≢0)
  (O^rf : String → DecTotalOrder.Carrier O → ℚ)
  (O^ev : String → DecTotalOrder.Carrier O → ℚ) where

open DecTotalOrder O renaming (Carrier to D; _≈_ to _≈D_; _≤_ to _≤D_)

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

composeSchedules2 : ∀ {l} {t : Set l} → List (List (D × t)) → List (D × t)
composeSchedules2 = mergeList (λ (x , _) (y , _) → x ≤? y)


distEvent : ∀ {l1 l2 l3} {d : Set l1} {i : Set l2} {t : Set l3} → (i → t) → List (d × i) → List (d × t)
distEvent f = map (λ (d , i) → d , f i)

compileSchedules : ∀ {l1 l2} {t : Set l1} → List (Σ (Set l2) λ i → (i → t) × List (D × i)) → List (D × t)
compileSchedules = mergeList (λ (x , _) (y , _) → x ≤? y) ∘ map (λ(_ , (f , l)) → distEvent f l)


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


X : Maybe String → String → D → ℚ
X (just CURS) CUR d = if does (CURS Data.String.≟ CUR) then 1ℚ else O^rf (concat (CURS ∷ "/" ∷ CUR ∷ [])) d
X nothing CUR d = 1ℚ


data FEB : Set where
  FEB_A : FEB
  FEB_N : FEB

FEB-≟ : (x y : FEB) → Dec (x ≡ y)
FEB-≟ FEB_A FEB_A = yes _≡_.refl
FEB-≟ FEB_N FEB_N = yes _≡_.refl
FEB-≟ FEB_A FEB_N = no λ()
FEB-≟ FEB_N FEB_A = no λ()



{- 
  Payoff Function:
    0.0
  State Transition Function:
    Ipac_{t^+ } = Ipac_{t^- } + Y (Sd_{t^- }1, t)Ipnr_{t^- } Nt_{t^- }
    Sd_{t^+ } = t
-}
PAM_AD_TRANS : ⊤ → D → ContractState → ContractState × ℚ
PAM_AD_TRANS _ d st = updateInterest d st , 0ℚ

PAM_AD_SCHED : List D → List (D × (ContractState → ContractState × ℚ))
PAM_AD_SCHED = map (λ d → d , PAM_AD_TRANS _ d)

{-
  Payoff Function:
    X^CURS_CUR(t) R(CNTRL) (-1) (NT + PDIED)
  State Transition Function:
    Nt_{t^+} = R(CNTRL)NT
    Ipnr_{t^+} = {
      0.0 if IPNR = ∅
      IPNR else
    }
    Ipac_{t^+} = {
      IPAC if IPAC != ∅
      y Nt_{t^+} Ipnr_{t^+} if IPANX != ∅ ∧ IPANX < t
      0.0 else
    }
    Sd_{t^+} = t
    with
    y = Y(IPANX, t)
-}
PAM_IED_TRANS : (Maybe String × String × ℚ × ℚ × Maybe ℚ × Maybe ℚ × Maybe D × ℚ) → D → ContractState → ContractState × ℚ
PAM_IED_TRANS (CURS , CUR , NT , RCNTRL , INPR , IPAC , IPANX , PDIED) d st = 
  let Nt' = RCNTRL * NT
      Ipnr' = fromMaybe 0ℚ INPR
      Ipac' = fromMaybe (maybe′ (λ IPANX → if does (IPANX ≤? d) then (yearFrac IPANX d * Nt' * Ipnr') else 0ℚ) 0ℚ IPANX) IPAC
  in record st { nt = Nt'; ipnr = Ipnr'; ipac = Ipac'; sd = d } , X CURS CUR d * (0ℚ - RCNTRL) * (NT + PDIED)

PAM_IED_SCHED : (Maybe String × String × ℚ × ℚ × Maybe ℚ × Maybe ℚ × Maybe D × ℚ) → 
  D → List (D × (ContractState → ContractState × ℚ))
PAM_IED_SCHED dat ied = (ied , PAM_IED_TRANS dat ied) ∷ []

{-
  Payoff Function:
    X^CURS_CUR(t) (Nsc_{t^- } Nt_{t^- } + Isc_{t^- } Ipac_{t^- } + Feac_{t^- } )
  State Transition Function:
    Nt_{t^+} = 0.0
    Ipac_{t^+} = 0.0
    Feac_{t^+} = 0.0
    Sd_{t^+} = t
-}
PAM_MD_TRANS : (Maybe String × String) → D → ContractState → ContractState × ℚ
PAM_MD_TRANS (CURS , CUR) d st = 
  record st { nt = 0ℚ; ipac = 0ℚ; feac = 0ℚ } , 
  X CURS CUR d * ((nsc st + nt st) * (isc st + ipac st) * feac st)

PAM_MD_SCHED : (Maybe String × String) → 
  D → List (D × (ContractState → ContractState × ℚ))
PAM_MD_SCHED dat MDt0 = (MDt0 , PAM_MD_TRANS dat MDt0) ∷ []


{-
Payoff Function:
  R(CNTRL) c if FEB = ’A’
  c Y(Sd_{t− }, t) Nt_{t− } + Feac_{t− } if FEB = ’N’
  where
  c = X^CURS_CUR(t) FER
State Transition Function:
  Ipac_{t^+} = Ipac_{t^- } + Y(Sd_{t^- }, t) Ipnr_{t^- } Nt_{t^- }
  Feac_{t^+} = 0
  Sd_{t^+} = t
Schedule
  t_vec^FP = ∅ if FER = ∅ ∨ FER = 0
             S(s, FECL, T^MD) else
  where
  s = ∅ if FEANX = ∅ ∧ FECL = ∅
      IED + FECL else if FEANX = ∅
      FEANX else
-}
PAM_FP_TRANS : (Maybe String × String × FEB × ℚ × ℚ) → D → ContractState → ContractState × ℚ
PAM_FP_TRANS (CURS , CUR , feb , FER , RCNTRL) t st =
  let
    Y_Sd_t = yearFrac (sd st) t
    c = X CURS CUR t * FER
    payoff = if does (FEB-≟ feb FEB_A) then RCNTRL * c
             else c * Y_Sd_t * (nt st) + (feac st)
    Ipac' = ipac st + Y_Sd_t * ipnr st * nt st
  in
    record st { ipac = Ipac' ; feac = 0ℚ ; sd = t } , payoff

FP_SCHEDULE : (Maybe String × String × FEB × Maybe ℚ × ℚ) → List D → List (D × (ContractState → ContractState × ℚ))
FP_SCHEDULE (CURS , CUR , feb , (just FER) , RCNTRL) dates =
  if ((FER ≤ᵇ 0ℚ) ∧ (0ℚ ≤ᵇ FER)) then []
  else map (\d → (d , PAM_FP_TRANS (CURS , CUR , feb , FER , RCNTRL) d)) dates
FP_SCHEDULE (CURS , CUR , feb , nothing , RCNTRL) dates = []


  -- if (does (FER ≟ nothing) ∨ does (FER ≟ just 0ℚ)) then []
  -- else 
  --     map (\d → (d , λ st → PAM_FP_TRANS d st)) dates

{-
Payoff Function:
  X^CURS_CUR(t) f(O^ev(CID, PP, t))
State Transition Function:
  Ipac_{t^+} = Ipac_{t^- } + Y(Sd_{t^- }, t) Ipnr_{t^- } Nt_{t^- }
  Feac_{t^+} = {
       Feac_{t^- } + Y(Sd_{t^- }, t) Nt_{t^- } FER if FEB = 'N'
       (Y(t^{FP- }, t) / Y(t^{FP- }, t^{FP+})) R(CNTRL) FER else
     }
  Nt_{t^+} = Nt_{t^- } - f(O^ev(CID, PP, t))
  Sd_{t^+} = t
  with
  t^{FP- } = sup t ∈ ~t^FP | t < t_0
  t^{FP+ } = inf t ∈ ~t^FP | t > t_0
-}
-- PAM_PP_TRANS : D → (Maybe ℚ × Maybe ℚ × ℚ) → ContractState → ContractState × ℚ
-- PAM_PP_TRANS d (OPANX , OPCL , IED) st = {!   !}

-- |FeeBasis
-- data FEB = FEB_A -- ^ Absolute value
--         | FEB_N -- ^ Notional of underlying
PAM_PP_TRANS :
  (Maybe String × String × FEB × ℚ × ℚ) →
  (t_FP_minus : D) → (t_FP_plus : D) → (d : D) → 
  ℤ.∣ ↥ yearFrac t_FP_minus t_FP_plus ∣ ≢0 →
  ContractState → ContractState × ℚ
PAM_PP_TRANS (CURS , CUR , feb , FER , RCNTRL) t_FP_minus t_FP_plus d nz st =
  let
    Y_Sd_d = yearFrac (sd st) d
    f_O_ev = O^ev "CID, PP" d
    Ipac' = ipac st + Y_Sd_d * ipnr st * nt st
    Feac' = if does (FEB-≟ feb FEB_N) then
              feac st + Y_Sd_d * nt st * FER
            else
              _÷_ (yearFrac t_FP_minus d) (yearFrac t_FP_minus t_FP_plus) {nz} * RCNTRL * FER
    Nt' = nt st - f_O_ev
  in
    record st { ipac = Ipac' ; feac = Feac' ; nt = Nt' ; sd = d } , X CURS CUR d * f_O_ev

_<D_ : (a b : D) → Dec (a ≤D b × ¬ (a ≈D b))
a <D b = {!   !}


createTransition : (TFPMinus TFPPlus : Maybe D) → (TFPMinus ≢ TFPPlus) → (Maybe String × String × FEB × ℚ × ℚ) → D → Maybe (D × (ContractState → ContractState × ℚ))
createTransition TFPMinus TFPPlus neq dat d  with TFPMinus | TFPPlus
... | nothing  | _         = nothing
... | _        | nothing   = nothing
... | just tFPminus | just tFPplus = 
    let nz = yearDist tFPminus tFPplus λ x → neq (cong just x) -- you need to provide a proof here that t_FP_minus ≠ t_FP_plus
    in just (d , PAM_PP_TRANS dat tFPminus tFPplus d nz)

PAM_PP_SCHEDULE :
  (Maybe String × String × FEB × ℚ × ℚ) → 
  (List D) → 
  (List D) → 
  List (D × (ContractState → ContractState × ℚ))
PAM_PP_SCHEDULE dat fpDates ppDates  =
  let
    TFPMinus d = last (filter (λ t → t ≤? d) fpDates)
    TFPPlus  d = head (filter (λ t → d <D t) fpDates)
    neq : ∀ d → TFPMinus d ≢ TFPPlus d
    neq = {!   !}
  in mapMaybe (λ d → createTransition (TFPMinus d) (TFPPlus d) (neq d) dat d) ppDates

PAM_ContractGen :
  D → 
  (Maybe String × String × ℚ × ℚ × Maybe ℚ × Maybe ℚ × Maybe D × ℚ × FEB × Maybe ℚ × ℚ × PRF) → 
  (List D) → D → D → (List D) → (List D) → 
  ContractState × List (D × (ContractState → ContractState × ℚ))
PAM_ContractGen 
  t0
  (CURS , CUR , NT , RCNTRL , INPR , IPAC , IPANX , PDIED , feb , FER , IPNR , prf)
  adDates iedDate mdDate fpDates ppDates =
  let
    feac = {!   !}

    startState = record
      { tmd = just mdDate
      ; nt = if does (t0 <D iedDate) then 0ℚ else RCNTRL * NT
      ; ipnr = if does (t0 <D iedDate) then 0ℚ else IPNR
      ; ipac = fromMaybe 0ℚ IPAC -- Note: IP schedule would need to be implemented for this
      ; ipac1 = nothing -- What should this actually be?
      ; ipac2 = nothing -- What should this actually be?
      ; ipla = nothing -- What should this actually be?
      ; feac = feac
      ; nsc = 1ℚ -- Note: Selectors must be implemented for this
      ; isc = 1ℚ -- Note: Selectors must be implemented for this
      ; prf = prf
      ; sd = t0 
      ; prnxt = 0ℚ -- What should this actually be?
      ; ipcb = 0ℚ -- What should this actually be?
      ; xd = nothing -- What should this actually be?
      ; xa = nothing -- What should this actually be?
      }
    AD_SCHED = PAM_AD_SCHED adDates
    IED_SCHED = PAM_IED_SCHED (CURS , CUR , NT , RCNTRL , INPR , IPAC , IPANX , PDIED) iedDate
    MD_SCHED = PAM_MD_SCHED (CURS , CUR) mdDate
    FP_SCHED = FP_SCHEDULE (CURS , CUR , feb , FER , RCNTRL) fpDates
    PP_SCHED = PAM_PP_SCHEDULE (CURS , CUR , feb , fromMaybe 0ℚ FER , RCNTRL) fpDates ppDates
  in
    startState , 
    composeSchedules2 (AD_SCHED ∷ IED_SCHED ∷ MD_SCHED ∷ FP_SCHED ∷ PP_SCHED ∷ [])

runContract : 
  ContractState → List (D × (ContractState → ContractState × ℚ)) →
  List (D × ℚ)
runContract st [] = []
runContract st ((d , tr) ∷ sch) with tr st
... | st' , o = (d , o) ∷ runContract st' sch

cashFlows : 
  D → 
  (Maybe String × String × ℚ × ℚ × Maybe ℚ × Maybe ℚ × Maybe D × ℚ × FEB × Maybe ℚ × ℚ × PRF) → 
  (List D) → D → D → (List D) → (List D) → 
  List (D × ℚ)
cashFlows t0 dat adDates iedDate mdDate fpDates ppDates =
  Data.Product.uncurry runContract (PAM_ContractGen t0 dat adDates iedDate mdDate fpDates ppDates)