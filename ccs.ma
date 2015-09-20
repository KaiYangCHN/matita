(**************************************************************************)
(*       ___                                                              *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||         The HELM team.                                      *)
(*      ||A||         http://helm.cs.unibo.it                             *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU General Public License Version 2                  *)
(*                                                                        *)
(**************************************************************************)
include "basics/types.ma".

inductive process : Type[0] ≝
  pro : process.

inductive action : Type[0] ≝
  | act : action
  | T : action.(* action internal *)

axiom transition : process → action → process → Prop .

(*An action is internal or no is determinable*)
axiom eqT_dec : ∀a : action. a = T ∨ a ≠ T.

(***************************** Derivatives ************************************)
(* Weak derivative *)
inductive weak_derivative : process →  action →  process → Prop ≝ 
  | eps : ∀p : process. weak_derivative p T p
  | w_single :
      ∀a : action.∀p,q : process.
      transition p a q → weak_derivative  p a q
  | w_tau_left :
      ∀a : action.∀p,p',q : process.
      transition p T p' → weak_derivative  p' a q → weak_derivative  p a q
  | w_tau_right :
      ∀a : action.∀p,q,q' : process.
      weak_derivative  p a q' → transition q' T q → weak_derivative  p a q.

(* Derivative *)
inductive derivative : process → action → process → Prop ≝ 
  | single :
      ∀a : action.∀p,q : process.
      transition p a q → derivative p a q
  | tau_left :
      ∀a : action.∀p,p',q : process.
      transition p T p' → derivative p' a q → derivative p a q
  | tau_right :
      ∀a : action.∀p,q,q' : process.
      derivative p a q' → transition q' T q → derivative p a q.

(* derivative → weak derivative *)
lemma deriv_weak_deriv :
  ∀p,p' : process.∀a : action.
  derivative p a p' → weak_derivative p a p'.
  #p #p' #a #H elim H
  [ #a0 #p0 #q #tr @w_single //
  | #a0 #p0 #p'' #q #tr #de #we @(w_tau_left … p'') //
  | #a0 #p0 #q #q' #de #tr #we @(w_tau_right … q') // 
  ]
qed.

(* a ≠ T → weak derivative → derivative *)
lemma weak_deriv_deriv :
  ∀p,p' : process.∀a : action.
  weak_derivative p a p' →  a ≠ T →  derivative p a p'.
  #p #p' #a #H elim H  
  [ #p0 #neqT elim neqT #H1 
    cut False
    [ /2/ 
    | #H2 elim H2 
    ]
  | #a0 #p0 #q #tr #H @single //
  | #a0 #p0 #p'' #q #tr #we #H_ind #neqT @(tau_left … p'') /2/
  | #a0 #p0 #q #q' #we #tr #H_ind #neqT @(tau_right … q') /2/
  ]
qed.

(* weak derivative T → weak derivative → weak derivative *)
lemma weak_deriv_tau_left :
  ∀p,p',p'' : process.∀a : action.
  weak_derivative p T p' → weak_derivative p' a p'' →  weak_derivative p a p''.
  cut
    (∀p,p' : process.∀a : action.
    weak_derivative p a p' → a = T → 
    ∀p'' : process.∀b : action.
    weak_derivative p' b p'' →  weak_derivative p b p'')
    [ #p #p' #a #H elim H
      [ #p0 #H' #p'' #b #we // 
      | #a0 #p0 #q #Tpq #eqT #p'' #b #we >eqT in Tpq; #tr @(w_tau_left … q) // 
      | #a0 #p0 #p'' #q #Tpq #we #H_rec #eqT #p''' #b #we' @(w_tau_left … p'') 
        [ // 
        | @(H_rec eqT p''' b we') 
        ] (* // @(H_rec...) can be replaced by /2/ *)
      | #a0 #p0 #q #q' #we #tr #H_rec #eqT #p'' #b #we' @(H_rec … eqT)
        @(w_tau_left … q) // 
      ]
    | #H #p #p' #p'' #a #we #we' @(H … p p' T we) // 
    ]
qed.

(* weak derivative → weak derivative T → weak derivative *)
lemma weak_deriv_tau_right :
  ∀p,p',p'' : process.∀a : action.
  weak_derivative p a p' → weak_derivative p' T p'' →  weak_derivative p a p''.
  cut
    (∀p',p'' : process.∀a : action.
    weak_derivative p' a p'' → a = T → 
    ∀p : process.∀b : action.
    weak_derivative p b p' →  weak_derivative p b p'')
    [ #p' #p'' #a #H elim H
      [ #p #eqT #p0 #b #we //
      | #a0 #p #q #tr #eqT #p0 #b #we >eqT in tr; @(w_tau_right … p) //
      | #a0 #p #p''' #q  #tr #we #H_rec #eqT #p0 #b #we' @(H_rec … eqT) 
        @(w_tau_right … p) //
      | #a0 #p #q #q' #we #tr #H_rec #eqT #p0 #b #we' @(w_tau_right … q') /2/ 
      ]
    | #H #p #p' #p'' #a #we #we' @(H … p' p'' T we') // 
    ]
qed.

(* weak derivative T → derivative → derivative *)
lemma w_deriv_tau_left :
  ∀p,p',p'' : process.∀a : action.
  weak_derivative p T p' →  derivative p' a p'' →  derivative p a p''.
  cut
    (∀p,p' : process.∀a : action.
    weak_derivative p a p' → a = T → 
    ∀p'' : process.∀b : action.
    derivative p' b p'' →  derivative p b p'')
    [ #p #p' #a #H elim H 
      [ #p0 #eqT #p'' #b #de // (*#p0..#de can be replaced by //*) 
      | #a0 #p0 #q #tr #eqT #p'' #b #de >eqT in tr; #tr @(tau_left … q) //
      | #a0 #p0 #p'' #q #tr #we #H_rec #eqT #p''' #b #de @(tau_left … p'') /2/
      | #a0 #p0 #q #q' #we #tr #H_rec #eqT #p'' #b #de /3/ 
      ] 
    (* /3/ can be replaced by  @(H_rec … eqT) @(tau_left … q) //*)
    | #H #p #p' #p'' #a #we #de @(H … p p' T we) //
    ] 
qed.

(* derivative → weak derivative T → derivative *)
lemma w_deriv_tau_right :
  ∀p,p',p'' : process.∀a : action.
  derivative p a p' →  weak_derivative p' T p'' →  derivative p a p''.
  cut
    (∀p',p'' : process.∀a : action.
    weak_derivative p' a p'' → a = T → 
    ∀p : process.∀b : action.derivative p b p' →  derivative p b p'')
    [ #p' #p'' #a #H elim H
      [ #p #eqT #p0 #b #de //
      | #a0 #p #q #tr #eqT #p0 #b #we @(tau_right … p) //
      | #a0 #p #p'' #q #tr #we #H_rec #eqT #p0 #b #de @(H_rec … eqT) @(tau_right … p)//
      | #a0 #p #q #q' #we #tr #H_rec #eqT #p0 #b #de @(tau_right … q') /2/ 
      ]
    | #H #p #p' #p'' #a #de #we @(H … p' p'' T) //
    ]
qed.

(* derivative T → derivative → derivative *)
lemma deriv_tau_left :
  ∀p,p',p'' : process.∀a : action.
  derivative p T p' →  derivative p' a p'' →  derivative p a p''.
  #p #p' #p'' #a #de #de' @(w_deriv_tau_left … p') /2/ 
qed.
(* "/2/" can be replaced by "// @(deriv_weak_deriv … de)" *) 

(* derivative → derivative T → derivative *)
lemma deriv_tau_right :
  ∀p,p',p'' : process.∀a : action.
  derivative p a p' →  derivative p' T p'' →  derivative p a p''.
  #p #p' #p'' #a #de #de' @(w_deriv_tau_right … p') /2/ 
qed. 
(* "/2/" can be replaced by "// @(deriv_weak_deriv … de')" *) 

(***** Strong equivalence : definition,reflexivity,symmetry,transitivity *****)
coinductive strong_eq : process →  process →  Prop ≝ 
  str_eq :
    ∀p,q : process.
    (∀a : action.∀p' : process.
    transition p a p' → 
    ∃q' : process. transition q a q' ∧ strong_eq p' q') →    
    (∀a : action.∀q' : process.
    transition q a q' → 
    ∃p' : process. transition p a p' ∧ strong_eq p' q') → 
    strong_eq p q.

(* Reflexivity *)
let corec refl_strong_eq : ∀p : process. strong_eq p p ≝ ?.
  #p @str_eq
  [ #a #p' #tr @(ex_intro … p') @conj // 
  | #a #q' #tr @(ex_intro … q') @conj // 
  ]
qed.

(* Symmetry *)
let corec sym_strong_eq : ∀p,q : process.strong_eq p q →  strong_eq q p ≝ ?.
  #p #q #st cases st #p0 #q0 #H0 #H1 @str_eq
  [ #a #p' #tr cases (H1 a p' tr)  #x * #tr #st @(ex_intro … x) @conj // 
    @sym_strong_eq @st
  | #a #q' #tr cases (H0 a q' tr)  #x * #tr #st @(ex_intro … x) @conj //  
    @sym_strong_eq @st 
  ]    
qed.

(* Transitivity *)
let corec trans_strong_eq :
  ∀p,q,r : process. strong_eq p q →  strong_eq q r →  strong_eq p r ≝ ?. 
  #p #q #r #pq #qr
  inversion pq #p0 #q0 #H1 #H2 #eq1 #eq2 
  inversion qr #p1 #q1 #H3 #H4 #eq3 #eq4
  @str_eq  
  [ #a #p' #tr cases (H1 a p' tr) #q1 * #Tq #strA
    cases (H3 a q1 ?) // 
    #r1 * #Tr #strB @(ex_intro … r1) @conj // 
    @trans_strong_eq //
  | #a #q' #tr cases (H4 a q' tr) #t1 * #Tt #strA
    cases (H2 a t1 ?) // 
    #p1 * #Tp #strB
    @(ex_intro … p1) @conj // 
    @trans_strong_eq //
  ]
qed. 

(****** Weak equivalence : definition,reflexivity,symmetry,transitivity ******)
coinductive weak_eq : process →  process →  Prop ≝ 
  w_eq :
    ∀p,q : process.
    (∀a : action.∀p' : process.
    transition p a p' → 
    ∃q' : process. weak_derivative q a q' ∧ weak_eq p' q') → 
    (∀a : action.∀q' : process.
    transition q a q' → 
    ∃p' : process. weak_derivative p a p' ∧ weak_eq p' q') → 
    weak_eq p q.

(* Reflexivity *)
let corec refl_weak_eq : ∀p : process. weak_eq p p ≝ ?. 
  #p @w_eq
  [ #a #p' #tr @(ex_intro … p') @conj /2/
  | #a #q' #tr @(ex_intro … q') @conj /2/ 
  ]
qed.

(* Symmetry *)
let corec sym_weak_eq : ∀p,q : process. weak_eq p q →  weak_eq q p ≝ ?.  
  #p #q #we cases we #p0 #q0 #H0 #H1 @w_eq
  [ #a #p' #tr cases (H1 a p' tr)  #x * #tr #st @(ex_intro … x) @conj // 
    @sym_weak_eq @st
  | #a #q' #tr cases (H0 a q' tr)  #x * #tr #st @(ex_intro … x) @conj //  
    @sym_weak_eq @st 
  ]
qed.

(* Be used to prove 'transitivity' *)
lemma Hint_Trans :
  ∀q,q',r : process.∀a : action.
  weak_derivative q a q' → 
  weak_eq q r →  ∃r' : process. weak_derivative r a r' ∧ weak_eq q' r'.
  #q #q' #r #a #we1 lapply r -r elim we1 
  [ #p #r #we2 %{r} /2/ 
  | #a0 #p #p' #Tp #r #Wepr inversion(Wepr) #p0 #q0 #Hp #Hq #Epp #Erq
    destruct @(Hp a0 p' Tp)
  | #a0 #p #p' #q0 #Tp #Wdp #Hind #r #Wepr
    cut(∃r''. weak_derivative r T r'' ∧ weak_eq p' r'')
      [ inversion(Wepr) #p0 #q1 #Hp0 #Hq1 #Epp0 #Erq1 destruct @(Hp0 T p' Tp)
      | * #r'' * #Tr #Wepr'
        cut(∃r'. weak_derivative r'' a0 r' ∧ weak_eq q0 r')
          [ @(Hind r'') //
          | * #r' * #Wdr #Weqr
            @(ex_intro … r') % /2/ 
          ]
      ]
  | #a0 #p #q0 #q0' #Wdp #Tq #Hind #r #Wepr
    cut(∃r''. weak_derivative r a0 r'' ∧ weak_eq q0' r'')
      [ @(Hind r Wepr)
      | *  #r'' * #Wdr #Weqr
        cut(∃r'. weak_derivative r'' T r' ∧ weak_eq q0 r')
          [ inversion(Weqr) #p0 #q1 #Hq0 #Hq1 #Epp0 #Erq1 destruct @(Hq0 T q0 Tq)
          | * #r' * #Wdr' #Weqr'
            @(ex_intro … r') % /2/ 
          ]
      ] 
  ] 
qed. 

(* Transitivity *)
let corec trans_weak_eq :
  ∀p,q,r : process. weak_eq p q →  weak_eq q r →  weak_eq p r ≝ ?. 
  #p #q #r #pq #qr @w_eq
  [ #a #p' #tr 
    cut (∃q' : process. weak_derivative q a q' ∧ weak_eq p' q')
      [ inversion pq #p0 #q0 #H1 #H2 #eq1 #eq2 
        < eq1 in H1; #H1 cases (H1 a p' tr) #x * #we # we1 @(ex_intro … x) @conj //
      | * #q' * #wd #we 
        cut (∃r' : process. weak_derivative r a r' ∧ weak_eq q' r')
          [ @(Hint_Trans q q' r) //
          | * #r' * #wd' #we' @(ex_intro … r') @conj // 
            @(trans_weak_eq … q') //
          ]
      ]
  | #a #r' #tr 
    cut (∃q' : process. weak_derivative q a q' ∧ weak_eq q' r')
      [ inversion qr #p0 #q0 #H1 #H2 #eq1 #eq2 
        < eq2 in H2; #H2 cases (H2 a r' tr) #x * #we # we1 @(ex_intro … x) @conj //
      | * #q' * #wd #we 
        cut (∃p' : process. weak_derivative p a p' ∧ weak_eq q' p')
          [ @(Hint_Trans q q' p) /2/
          | * #p' * #wd' #we' @(ex_intro … p') @conj // 
            @(trans_weak_eq … q') /2/
          ]
      ]
  ]
qed.
(********* weaq_eq1 : an equivalent definition for weak equivalence **********)
coinductive weak_eq1 : process →  process →  Prop ≝ 
  w_eq1 :
    ∀p,q : process.
    (∀a : action.∀p' : process.
    derivative p a p' → 
    ∃q' : process. weak_derivative q a q' ∧ weak_eq1 p' q') → 
    (∀a : action.∀q' : process.
    derivative q a q' → 
    ∃p' : process. weak_derivative p a p' ∧ weak_eq1 p' q') → 
    weak_eq1 p q.

(* Be used to prove weak_eq_deriv_sym *)
lemma weak_eq_deriv :
  ∀p,q : process.
  weak_eq p q → 
  ∀a : action.∀p' : process.
  derivative p a p' → 
  ∃q' : process. weak_derivative q a q' ∧ weak_eq p' q'. 
  #p #q #we #a #p' #de lapply we -we lapply q -q elim de -de -a -p -p'
  [ #a #p #p' #tr #q #we inversion we #p0 #q0 #H1 #H2 #eq1 #eq2 destruct
    cases (H1 a p' tr) #x * #we1 #we' @(ex_intro … x) @conj //
  | #a #p #p1 #p' #tr #de #H_ind #q #we
    cut (∃q1 : process. weak_derivative q T q1 ∧ weak_eq p1 q1)
      [ inversion we #p0 #q0 #H1 #H2 #eq1 #eq2 @(H1 T p1) //
      | * #q1 * #wde #we' 
        cut (∃q' : process. weak_derivative q1 a q' ∧ weak_eq p' q')
          [ @(H_ind q1) /2/
          | * #q' * #wde1 #we1 @(ex_intro … q') @conj /2/ 
          ]
      ]
  | #a #p #p' #p1 #tr #de #H_ind #q #we
    cut (∃q1 : process. weak_derivative q a q1 ∧ weak_eq p1 q1)
      [ @(H_ind q we)
      | * #q1 * #wde #we1
        cut (∃q' : process. weak_derivative q1 T q' ∧ weak_eq p' q')
          [ inversion we1 #p0 #q0 #H1 #H2 #eq1 #eq2 @(H1 T p') /2/
          | * #q' * #wde1 #we' @(ex_intro … q') @conj /2/ 
          ]
      ]
  ]      
qed.

(* Be used to prove 'weak eq → weak eq1' *)
lemma weak_eq_deriv_sym :
  ∀p,q : process.
  weak_eq p q → 
  ∀a : action.∀q' : process.
  derivative q a q' → 
  ∃p' : process. weak_derivative p a p' ∧ weak_eq p' q'.
  #p #q #we #a #q' #de 
  cut (weak_eq q p)
    [ @(sym_weak_eq p q we)
    | #we' cases (weak_eq_deriv q p we' a q' de) #p' * #w_de #we'' 
      @(ex_intro … p') @conj // 
      @(sym_weak_eq … we'') 
    ]
qed.

(* weak eq1 → weak eq *)       
let corec weak_eq1_weak_eq : ∀p,q : process. weak_eq1 p q →  weak_eq p q ≝ ?.
  #p #q #we1 cases we1 #p0 #q0 #H1 #H2 @w_eq
  [ #a #p' #tr cases (H1 a p' ?)
    [ #x * #H3 #H4 @(ex_intro … x) @conj //
      @weak_eq1_weak_eq // 
    | /2/ 
    ]
  | #a #q' #tr cases (H2 a q' ?)
    [ #x * #H3 #H4 @(ex_intro … x) @conj // 
      @weak_eq1_weak_eq // 
    | /2/ 
    ]
  ]
qed.

(* weak eq → weak eq1 *)
let corec weak_eq_weak_eq1 : ∀p,q : process. weak_eq p q →  weak_eq1 p q ≝ ?.
  #p #q #we @w_eq1 
  [ #a #p' #de cases (weak_eq_deriv p q we a p' de) #x * #we' #we1 
    @(ex_intro … x) @conj //
    @weak_eq_weak_eq1 // 
  | #a #q' #de cases (weak_eq_deriv_sym p q we a q' de) #x * #we' #we1 
    @(ex_intro … x) @conj //   
    @weak_eq_weak_eq1 // 
  ]
qed.  

(* Reflexivity *)
lemma refl_weak_eq1 : ∀p : process. weak_eq1 p p.
  #p @weak_eq_weak_eq1 @refl_weak_eq
qed.

(* Symmetry *)
lemma sym_weak_eq1 : ∀p,q : process. weak_eq1 p q →  weak_eq1 q p.
  #p #q #H @weak_eq_weak_eq1 @sym_weak_eq @weak_eq1_weak_eq // 
qed.

(* Transitivity *)
lemma trans_weak_eq1 :
  ∀p,q,r : process. weak_eq1 p q →  weak_eq1 q r →  weak_eq1 p r.
  #p #q #r #we1 #we2 @weak_eq_weak_eq1 @(trans_weak_eq … q) /2/ 
qed.
(******** Observational equivalence : definition,reflexivity,symmetry *********)
inductive obs_eq (p,q : process) : Prop ≝ 
  obs:(∀a : action.∀p' : process.
    transition p a p' → 
    ∃q' : process. derivative q a q' ∧ weak_eq p' q') ∧
    (∀a : action.∀q' : process.
    transition q a q' → 
    ∃p' : process. derivative p a p' ∧ weak_eq p' q')→ obs_eq p q.

(* Reflexivity *)
lemma refl_obs_eq : ∀p : process. obs_eq p p.
  #p @obs @conj
  [ #a #p' #tr @(ex_intro … p') @conj /2/
  | #a #q' #tr @(ex_intro … q') @conj /2/
qed.

(* Symmetry *)
lemma sym_obs_eq : ∀p,q : process. obs_eq p q →  obs_eq q p.
  #p #q #ob cases ob * #H1 #H2 @obs @conj 
  [ #a #p' #tr cases (H2 a p' tr) #x * #de #we @(ex_intro … x) @conj /2/
  | #a #q' #tr cases (H1 a q' tr) #x * #de #we @(ex_intro … x) @conj /2/
  ]
qed.

(****** obs_eq1 : an equivalent definition for observational equivalence ******)
inductive obs_eq1 (p,q : process) : Prop ≝ 
  obs1:
    (∀a : action.∀p' : process.
    derivative p a p' → 
    ∃q' : process. derivative q a q' ∧ weak_eq p' q') ∧
    (∀a : action.∀q' : process.
    derivative q a q' → 
    ∃p' : process. derivative p a p' ∧ weak_eq p' q') → obs_eq1 p q.

(* By proving obs_eq1 → obs_eq and obs_eq → obs_eq1,we prove these two relations
   are equivalent *)
lemma obs_eq1_obs_eq : ∀p,q : process. obs_eq1 p q →  obs_eq p q.
  #p #q #oe cases oe * #H1 #H2 @obs @conj
  [ #a #p' #tr @H1 @single //
  | #a #q' #tr @H2 @single //
  ]
qed.

(* Be used to prove the lemma 'obs eq → obs eq1' *)
lemma half_obs_eq_obs_eq1 :
  ∀p,q : process. obs_eq p q → 
  ∀a : action.∀p' : process.
  derivative p a p' →  ∃q' : process. derivative q a q' ∧ weak_eq p' q'.
  #p #q #oe #a #p' #de lapply oe lapply q -oe -q
  elim de -de -a -p -p'
  [ #a #p #p' #tr #q #oe elim oe * #H1 #H2 /2/
  | #a #p #p1 #p' #tr #de #H_ind #q #oe
    cut (∃q1 : process. derivative q T q1 ∧ weak_eq p1 q1)
      [ elim oe * #H1 #H2 /2/
      | * #q1 * #de' #we
        cut (∃q' : process. weak_derivative q1 a q' ∧ weak_eq p' q')
          [ cut (weak_eq1 p1 q1) /2/ 
          | * #q' * #de'' #we' @(ex_intro … q') @conj //
            elim (eqT_dec … a)
              [ #a_T destruct @(w_deriv_tau_right … q1) //
              | #dif_a_T @(weak_deriv_deriv) 
                [ @(weak_deriv_tau_left … q1) /2/ 
                ] 
                // 
              ] 
          ]
       ]   
  | #a #p #p' #p1 #de #tr #H_ind #q #oe 
    cut (∃q1 : process. derivative q a q1 ∧ weak_eq p1 q1)
      [ @(H_ind … q) // 
      | * #q1 * #de1 #we1 
        cut (∃q' : process. weak_derivative q1 T q' ∧ weak_eq p' q')
          [ inversion we1 #p0 #q0 #H1 #H2 #eq1 #eq2 destruct cases (H1 T p' tr) 
            #x * #we2 #we @(ex_intro … x) @conj //
          | * #q' * #de2 #we @(ex_intro … q') @conj /2/ 
          ]
      ]
  ]
qed.

(* obs eq → obs eq1 *)
lemma obs_eq_obs_eq1 : ∀p,q : process. obs_eq p q →  obs_eq1 p q. 
  #p #q #oe @obs1 @conj
  [ #a #p' #de @(half_obs_eq_obs_eq1 p q oe a p' de) 
  | cut
      (∀a : action.∀q' : process.
      derivative q a q'→∃p' : process.derivative p a p' ∧ weak_eq q' p')
      (* can't use half_obs_eq_eq1 directly,because the second part of the 
         original definition of half_obs_eq_eq1 is weak_eq q' p',so use 'cut' *)
      [ cut(obs_eq q p) 
      (* to prove the versa forma so introduce the versa forma of obs_eq pq *)
          [ @sym_obs_eq //
          | #oe' @(half_obs_eq_obs_eq1 q p) // 
          ]
      | #H #a #q' #de cases (H a q' de) #x * #H1 #H2 @(ex_intro … x) @conj /2/
      ]
  ]   
qed.
  
(* Reflexivity of obe_eq1 *)
lemma refl_obs_eq1 : ∀p : process. obs_eq1 p p.
  #p @obs1 @conj #a 
  [ #p' #de @(ex_intro … p') @conj /2/ 
  | #q' #de @(ex_intro … q') @conj /2/ 
  ]
qed.

(* Symmetry of obe_eq1 *)
lemma sym_obs_eq1 : ∀p,q : process. obs_eq1 p q →  obs_eq1 q p.
  #p #q #ob @obs_eq_obs_eq1 @sym_obs_eq /2/ 
qed. 

(* Be used to prove transitivity of obe_eq1 *)
lemma half_trans_obs_eq1 :
  ∀p,q,r : process.
  obs_eq1 p q →
  obs_eq1 q r →
  ∀a : action.∀p' : process.
  derivative p a p' → ∃r' : process. derivative r a r' ∧ weak_eq p' r'.
  #p #q #r #pq #qr #a #p' #de
  (* using |pq| and |de| ,we can get |derivative q a q' ∧ weak_eq p' q'|,
     using the first part and |qr| we can get |derivative r a r' ∧ weak_eq q' r'|,
     using the second part and |weak_eq p' q'| we can get |weak_eq p' r'| 
     so introduce |derivative q a q' ∧ weak_eq p' q'| then we can use |pq| |qr|.
  *)
  cut (∃q' : process. derivative q a q' ∧ weak_eq p' q')
    [ cases pq * #H1 #H2 @(H1 a p' de)
    | * #r * #de' #we cases qr * #H1 #H2
      cases (H1 a r de') #r' * #de'' #we' @(ex_intro … r') @conj /2/
    ]  
qed.

(* Transitivity of obe_eq1 *)
lemma trans_obs_eq1 :
  ∀p,q,r : process. obs_eq1 p q →  obs_eq1 q r →  obs_eq1 p r.
  #p #q #r #pq #qr @obs1 @conj
  [ #a #p' #de @(half_trans_obs_eq1 p q r pq qr a p' de)
  | #a #r' #de
    (* introduce obs_eq1 q p and obe_eq1 r q,then can use half_trans_obs_eq1 *)
    cut (obs_eq1 q p) /2/ 
    cut (obs_eq1 r q) /2/ 
    #rq #qp cases (half_trans_obs_eq1 r q p rq qp a r' de) #p' * #de' #we
    @(ex_intro … p') @conj /2/
  ]
qed.

(* Transitivity of obs_eq,using the results of obs_eq1 *)
lemma trans_obs_eq :
  ∀p,q,r : process. obs_eq p q → obs_eq q r → obs_eq p r.
  #p #q #r #pq #qr @obs_eq1_obs_eq @(trans_obs_eq1 … q) /2/ 
qed.

(******************** Strong_eq → Obs_eq → Weak_eq **************************)
(* strong_eq is stronger than weak_eq *)
let corec strong_weak : ∀p,q : process. strong_eq p q →  weak_eq p q ≝ ?.
  #p #q #st cases st #p0 #q0 #H1 #H2 @w_eq 
  [ #a #p' #tr cases (H1 a p' tr) #x * #H3 #H4 @(ex_intro … x) @conj
    [ @w_single // 
    | @strong_weak @H4 
    ]
  | #a #q' #tr cases (H2 a q' tr) #x * #H3 #H4 @(ex_intro … x) @conj
    [ @w_single // 
    | @strong_weak @H4 
    ]
  ]
qed. 

(* strong_eq is stronger than obs_eq *)
lemma strong_obs : ∀p,q : process. strong_eq p q →  obs_eq p q.
  #p #q #st cases st #p0 #q0 #H1 #H2 @obs @conj 
  [ #a #p' #tr cases (H1 a p' tr) #x * #tr' #st' @(ex_intro … x) @conj
    [ @single // 
    | @strong_weak // 
    ]
  | #a #q' #tr cases (H2 a q' tr) #x * #tr' #st' @(ex_intro … x) @conj
    [ @single //
    | @strong_weak // 
    ]
  ]
qed. 

(* obs_eq is stronger than weak_eq *)
lemma obs_weak : ∀p,q : process. obs_eq p q →  weak_eq p q.
  #p #q #ob cases ob * #H1 #H2 @w_eq
  [ #a #p' #tr cases (H1 a p' tr) #x * #de #we @(ex_intro … x) @conj /2/
  | #a #q' #tr cases (H2 a q' tr) #x * #de #we @(ex_intro … x) @conj /2/
  ]
qed.