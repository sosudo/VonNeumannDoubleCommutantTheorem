import Architect
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.LocallyConvex.WeakOperatorTopology
import Mathlib.Analysis.VonNeumannAlgebra.Basic
namespace VonNeumannDoubleCommutantTheorem

open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A centralizer is WOT-closed: express its commutation equations using continuous matrix coefficients. -/
@[blueprint "VonNeumannDoubleCommutantTheorem.MainTheorem"]
lemma centralizer_wot_closed (s : Set (H →L[ℂ] H)) :
    IsClosed ((ContinuousLinearMap.toWOT (RingHom.id ℂ) H H) '' Set.centralizer s) := by
  let e := ContinuousLinearMap.toWOT (RingHom.id ℂ) H H
  have he : e '' Set.centralizer s = {T | ∀ A ∈ s, ∀ x (y : StrongDual ℂ H), y (A (T x)) = y (T (A x))} := by
    ext T
    constructor
    · rintro ⟨B, hB, rfl⟩ A hA x y
      have h := hB A hA
      have hx := congrArg (fun f : H →L[ℂ] H => f x) h
      simpa using congrArg y hx
    · intro h
      refine ⟨e.symm T, ?_, e.apply_symm_apply T⟩
      intro A hA
      ext x
      apply (separatingDual_iff_injective.mp (inferInstance : SeparatingDual ℂ H))
      ext y
      exact h A hA x y
  rw [he]
  simp_rw [Set.setOf_forall]
  apply isClosed_iInter fun A => isClosed_iInter fun hA => isClosed_iInter fun x => isClosed_iInter fun y => ?_
  exact isClosed_eq (ContinuousLinearMapWOT.continuous_dual_apply x (y.comp A))
    (ContinuousLinearMapWOT.continuous_dual_apply (A x) y)

open ContinuousLinearMap
/-- The coordinatewise action on a product. -/
@[blueprint "VonNeumannDoubleCommutantTheorem.MainTheorem"]
noncomputable def diagOp {ι : Type*} (A : H →L[ℂ] H) : (ι → H) →L[ℂ] (ι → H) :=
  ContinuousLinearMap.pi fun i => A.comp (ContinuousLinearMap.proj i)

/-- The product action acts coordinatewise, by definition. -/
@[blueprint "VonNeumannDoubleCommutantTheorem.MainTheorem"]
lemma diagOp_apply {ι : Type*} (A : H →L[ℂ] H) (x : ι → H) (i : ι) :
    diagOp A x i = A (x i) := rfl

/-- The diagonal action preserves single-coordinate vectors, by extensionality. -/
@[blueprint "VonNeumannDoubleCommutantTheorem.MainTheorem"]
lemma diag_single {ι : Type*} [DecidableEq ι] (A : H →L[ℂ] H) (j : ι) (x : H) :
    diagOp A (Pi.single j x) = Pi.single j (A x) := by
  ext i
  by_cases h : i = j <;> simp [diagOp_apply, Pi.single_apply, h, eq_comm]

/-- A bicommutant element commutes with every operator commuting with the diagonal algebra: use matrix coefficients. -/
@[blueprint "VonNeumannDoubleCommutantTheorem.MainTheorem"]
lemma diag_commutes {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (T : H →L[ℂ] H)
    (hT : T ∈ Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))))
    (P : (ι → H) →L[ℂ] (ι → H))
    (hP : ∀ A ∈ S, diagOp A * P = P * diagOp A) :
    diagOp T * P = P * diagOp T := by
  have hblock (i j : ι) : ((proj i).comp (P.comp (single ℂ (fun _ : ι => H) j))) ∈
      Set.centralizer (S : Set (H →L[ℂ] H)) := by
    intro A hA
    ext x
    have h := DFunLike.congr_fun (hP A hA) (single ℂ (fun _ : ι => H) j x)
    have hi := congrFun h i
    simpa [diagOp_apply, ← mul_def, Function.comp_def, diag_single] using hi
  ext v i
  have hv : (∑ j, (single ℂ (fun _ : ι => H) j) (v j)) = v := by
    ext j
    simp
  conv_lhs => rw [← hv]
  conv_rhs => rw [← hv]
  simp only [← mul_def, comp_apply, diagOp_apply, map_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j hj
  have hjj := DFunLike.congr_fun (hT _ (hblock i j)) (v j)
  simpa [← mul_def, diagOp_apply, diag_single] using hjj.symm

/-- The diagonal action on the finite Hilbert direct sum. -/
@[blueprint "VonNeumannDoubleCommutantTheorem.MainTheorem"]
noncomputable def lpDiag {ι : Type*} [Fintype ι] (A : H →L[ℂ] H) :
    (PiLp 2 (fun _ : ι => H)) →L[ℂ] (PiLp 2 (fun _ : ι => H)) :=
  let e := PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => H)
  e.symm.toContinuousLinearMap.comp ((diagOp A).comp e.toContinuousLinearMap)

/-- The Hilbert direct-sum action acts coordinatewise, by definition. -/
@[blueprint "VonNeumannDoubleCommutantTheorem.MainTheorem"]
lemma lpDiag_apply {ι : Type*} [Fintype ι] (A : H →L[ℂ] H) (v : PiLp 2 (fun _ : ι => H)) (i : ι) :
    lpDiag A v i = A (v i) := rfl

/-- Diagonal commutation on the Hilbert direct sum follows by conjugation to the product. -/
@[blueprint "VonNeumannDoubleCommutantTheorem.MainTheorem"]
lemma lpDiag_commutes {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (T : H →L[ℂ] H)
    (hT : T ∈ Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))))
    (P : (PiLp 2 (fun _ : ι => H)) →L[ℂ] (PiLp 2 (fun _ : ι => H)))
    (hP : ∀ A ∈ S, lpDiag A * P = P * lpDiag A) :
    lpDiag T * P = P * lpDiag T := by
  let e := PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => H)
  let Q := e.toContinuousLinearMap.comp (P.comp e.symm.toContinuousLinearMap)
  have hQ : ∀ A ∈ S, diagOp A * Q = Q * diagOp A := by
    intro A hA
    ext v i
    have hv := DFunLike.congr_fun (hP A hA) (e.symm v)
    have hi := congrArg (fun z : PiLp 2 (fun _ : ι => H) => z i) hv
    simpa [Q, e, ← mul_def, lpDiag_apply, diagOp_apply] using hi
  have hh := diag_commutes S T hT Q hQ
  ext v i
  have hv := DFunLike.congr_fun hh (e v)
  have hi := congrFun hv i
  simpa [Q, e, ← mul_def, lpDiag_apply, diagOp_apply] using hi

/-- The diagonal action preserves adjoints: calculate inner products coordinatewise. -/
@[blueprint "VonNeumannDoubleCommutantTheorem.MainTheorem"]
lemma lpDiag_star {ι : Type*} [Fintype ι] (A : H →L[ℂ] H) :
    lpDiag (ι := ι) (star A) = star (lpDiag (ι := ι) A) := by
  change lpDiag (ι := ι) A.adjoint = (lpDiag (ι := ι) A).adjoint
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  simp only [PiLp.inner_apply, lpDiag_apply, ContinuousLinearMap.adjoint_inner_left]

/-- Diagonal amplification preserves bicommutant membership, by the matrix-coefficient argument. -/
@[blueprint "VonNeumannDoubleCommutantTheorem.MainTheorem"]
lemma lpDiag_bicommutant {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (T : H →L[ℂ] H)
    (hT : T ∈ Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H)))) :
    lpDiag (ι := ι) T ∈ Set.centralizer (Set.centralizer (lpDiag (ι := ι) '' (S : Set (H →L[ℂ] H)))) := by
  intro P hP
  exact (lpDiag_commutes S T hT P (by
    intro A hA
    exact hP _ ⟨A, hA, rfl⟩)).symm

/-- The diagonal action as a star-algebra homomorphism. -/
@[blueprint "VonNeumannDoubleCommutantTheorem.MainTheorem"]
noncomputable def lpDiagHom (ι : Type*) [Fintype ι] :
    (H →L[ℂ] H) →⋆ₐ[ℂ] (PiLp 2 (fun _ : ι => H) →L[ℂ] PiLp 2 (fun _ : ι => H)) where
  toFun := lpDiag
  map_one' := by ext x i; simp [lpDiag_apply]
  map_mul' A B := by ext x i; simp [lpDiag_apply, ← mul_def]
  map_zero' := by ext x i; simp [lpDiag_apply]
  map_add' A B := by ext x i; simp [lpDiag_apply]
  commutes' r := by ext x i; simp [lpDiag_apply, Algebra.algebraMap_eq_smul_one]
  map_star' := lpDiag_star

/-- The amplified element belongs to the bicommutant of the mapped algebra. -/
@[blueprint "VonNeumannDoubleCommutantTheorem.MainTheorem"]
lemma lpDiag_bicommutant_map {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (T : H →L[ℂ] H)
    (hT : T ∈ Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H)))) :
    lpDiag (ι := ι) T ∈ Set.centralizer (Set.centralizer
      ((S.map (lpDiagHom ι)) : Set (PiLp 2 (fun _ : ι => H) →L[ℂ] PiLp 2 (fun _ : ι => H)))) := by
  exact lpDiag_bicommutant S T hT
/-- The projection onto an invariant subspace commutes with the star algebra: use invariance under operators and adjoints. -/
@[blueprint "VonNeumannDoubleCommutantTheorem.MainTheorem"]
lemma proj_commutes (S : StarSubalgebra ℂ (H →L[ℂ] H)) (K : Submodule ℂ H)
    [K.HasOrthogonalProjection] (h : ∀ a ∈ S, K ∈ Module.End.invtSubmodule a.toLinearMap) :
    K.starProjection ∈ Set.centralizer (S : Set (H →L[ℂ] H)) := by
  intro a ha
  have he := isStarProjection_starProjection (U := K)
  have h1 := (he.isIdempotentElem.range_mem_invtSubmodule_iff (T := a)).mp (by simpa using h a ha)
  have h2 := (he.isIdempotentElem.range_mem_invtSubmodule_iff (T := star a)).mp (by simpa using h (star a) (star_mem ha))
  have h3 : K.starProjection * a * K.starProjection = K.starProjection * a := by
    simpa [he.isSelfAdjoint.star_eq, ← mul_def] using congr(star $h2)
  simpa [← mul_def] using (h3.symm.trans h1).symm

/-- A bicommutant element preserves every closed invariant subspace, since it commutes with its projection. -/
@[blueprint "VonNeumannDoubleCommutantTheorem.MainTheorem"]
lemma bicommutant_invariant (S : StarSubalgebra ℂ (H →L[ℂ] H)) (K : Submodule ℂ H)
    [K.HasOrthogonalProjection] (h : ∀ a ∈ S, K ∈ Module.End.invtSubmodule a.toLinearMap)
    {T : H →L[ℂ] H} (hT : T ∈ Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H)))) :
    K ∈ Module.End.invtSubmodule T.toLinearMap := by
  rw [Module.End.mem_invtSubmodule]
  intro x hx
  have hp := proj_commutes S K h
  have hc := hT K.starProjection hp
  have heq : K.starProjection (T x) = T x := by
    have hx' : K.starProjection x = x := K.starProjection_eq_self_iff.mpr hx
    have hc' := DFunLike.congr_fun hc x
    simpa [← mul_def, hx'] using hc'
  change T x ∈ K
  rw [← heq]
  exact K.starProjection_apply_mem (T x)

open scoped Topology
open Filter
/-- Finite simultaneous strong approximation implies weak-operator closure, using the generating matrix coefficients. -/
@[blueprint "VonNeumannDoubleCommutantTheorem.MainTheorem"]
lemma finite_strong_to_wot (S : StarSubalgebra ℂ (H →L[ℂ] H)) (T : H →L[ℂ] H)
    (h : ∀ (I : Finset (H × StrongDual ℂ H)),
      (fun p : I => T p.1.1) ∈ closure {v : I → H | ∃ a ∈ S, v = fun p => a p.1.1}) :
    ContinuousLinearMap.toWOT (RingHom.id ℂ) H H T ∈
      closure ((ContinuousLinearMap.toWOT (RingHom.id ℂ) H H) '' (S : Set (H →L[ℂ] H))) := by
  rw [ContinuousLinearMapWOT.isInducing_inducingFn.closure_eq_preimage_closure_image]
  change _ ∈ closure _
  apply mem_closure_iff_nhds.mpr
  intro U hU
  rw [nhds_pi, Filter.mem_pi'] at hU
  obtain ⟨I, V, hV, hVU⟩ := hU
  let W : Set (I → H) := {v | ∀ p : I, p.1.2 (v p) ∈ V p.1}
  have hW : W ∈ 𝓝 (fun p : I => T p.1.1) := by
    simp only [W, Set.setOf_forall]
    apply Filter.iInter_mem.mpr
    intro p
    exact ((p.1.2.continuous.comp (continuous_apply p)).continuousAt.preimage_mem_nhds (hV p.1))
  obtain ⟨v, hvW, a, ha, rfl⟩ := mem_closure_iff_nhds.mp (h I) W hW
  refine ⟨(ContinuousLinearMapWOT.inducingFn (RingHom.id ℂ) H H) ((ContinuousLinearMap.toWOT (RingHom.id ℂ) H H) a), hVU ?_, ?_⟩
  · intro p hp
    exact hvW ⟨p,hp⟩
  · exact ⟨_, ⟨a, ha, rfl⟩, rfl⟩

/-- Hilbert direct-sum orbit closure implies product orbit closure by continuity of the coordinate equivalence. -/
@[blueprint "VonNeumannDoubleCommutantTheorem.MainTheorem"]
lemma piLp_closure_to_pi {I : Type*} [Fintype I] (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (x : I → H) (T : H →L[ℂ] H)
    (h : (WithLp.toLp 2 (fun i => T (x i)) : PiLp 2 (fun _ : I => H)) ∈
      closure {v : PiLp 2 (fun _ : I => H) | ∃ a ∈ S, v = WithLp.toLp 2 (fun i => a (x i))}) :
    (fun i => T (x i)) ∈ closure {v : I → H | ∃ a ∈ S, v = fun i => a (x i)} := by
  have hm : (fun i => T (x i)) ∈ closure (Set.image (fun (v : PiLp 2 (fun _ : I => H)) => WithLp.ofLp v) {v : PiLp 2 (fun _ : I => H) | ∃ a ∈ S, v = WithLp.toLp 2 (fun i => a (x i))}) :=
    image_closure_subset_closure_image (PiLp.continuous_ofLp 2 (fun _ : I => H)) (Set.mem_image_of_mem _ h)
  apply closure_mono _ hm
  rintro v ⟨w, ⟨a, ha, rfl⟩, rfl⟩
  exact ⟨a, ha, rfl⟩

/-- Finite amplification and the cyclic orbit property imply the theorem; centralizers give the converse. -/
@[blueprint "VonNeumannDoubleCommutantTheorem.MainTheorem"]
lemma assembly (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (hcyclic : ∀ (I : Finset (H × StrongDual ℂ H))
      (T : (PiLp 2 (fun _ : I => H)) →L[ℂ] (PiLp 2 (fun _ : I => H))),
      T ∈ Set.centralizer (Set.centralizer ((S.map (lpDiagHom I)) : Set _)) →
      ∀ x, T x ∈ closure {v | ∃ a ∈ S.map (lpDiagHom I), v = a x}) :
    IsClosed ((ContinuousLinearMap.toWOT (RingHom.id ℂ) H H) '' (S : Set (H →L[ℂ] H))) ↔
      Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))) = (S : Set (H →L[ℂ] H)) := by
  classical
  constructor
  · intro hclosed
    apply Set.Subset.antisymm
    · intro T hT
      have hW : ContinuousLinearMap.toWOT (RingHom.id ℂ) H H T ∈
          closure ((ContinuousLinearMap.toWOT (RingHom.id ℂ) H H) '' (S : Set (H →L[ℂ] H))) := by
        apply finite_strong_to_wot S T
        intro I
        apply piLp_closure_to_pi S (fun p : I => p.1.1) T
        have ht := hcyclic I (lpDiag T) (lpDiag_bicommutant_map S T hT) (WithLp.toLp 2 (fun p : I => p.1.1))
        apply closure_mono _ ht
        rintro v ⟨a, ha, rfl⟩
        obtain ⟨b, hb, rfl⟩ := StarSubalgebra.mem_map.mp ha
        refine ⟨b, hb, ?_⟩
        ext i
        rfl
      have hmem := hclosed.closure_subset hW
      obtain ⟨A, hA, hAT⟩ := hmem
      have : A = T := (ContinuousLinearMap.toWOT (RingHom.id ℂ) H H).injective hAT
      simpa [this] using hA
    · exact Set.subset_centralizer_centralizer (S := (S : Set (H →L[ℂ] H)))
  · intro h
    rw [← h]
    exact centralizer_wot_closed _
/-- The orbit of a vector under a unital algebra as a linear subspace. -/
@[blueprint "VonNeumannDoubleCommutantTheorem.MainTheorem"]
noncomputable def orbitSub (S : StarSubalgebra ℂ (H →L[ℂ] H)) (x : H) : Submodule ℂ H where
  carrier := {y | ∃ a ∈ S, a x = y}
  zero_mem' := ⟨0, S.zero_mem, by simp⟩
  add_mem' := by
    rintro u v ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a+b, S.add_mem ha hb, by simp⟩
  smul_mem' := by
    rintro r u ⟨a, ha, rfl⟩
    exact ⟨r • a, S.smul_mem ha r, by simp⟩

/-- The orbit is invariant under the algebra, by multiplication. -/
@[blueprint "VonNeumannDoubleCommutantTheorem.MainTheorem"]
lemma orbit_invariant (S : StarSubalgebra ℂ (H →L[ℂ] H)) (x : H) (a : H →L[ℂ] H) (ha : a ∈ S) :
    Set.MapsTo a (orbitSub S x : Set H) (orbitSub S x : Set H) := by
  rintro y ⟨b, hb, rfl⟩
  exact ⟨a*b, S.mul_mem ha hb, rfl⟩

/-- The orbit closure is invariant by continuity. -/
@[blueprint "VonNeumannDoubleCommutantTheorem.MainTheorem"]
lemma orbit_closure_invariant (S : StarSubalgebra ℂ (H →L[ℂ] H)) (x : H) (a : H →L[ℂ] H) (ha : a ∈ S) :
    Set.MapsTo a (closure (orbitSub S x : Set H)) (closure (orbitSub S x : Set H)) :=
  (orbit_invariant S x a ha).closure a.continuous

/-- A bicommutant element sends a vector into the closure of its orbit, using the invariant-subspace projection. -/
@[blueprint "VonNeumannDoubleCommutantTheorem.MainTheorem"]
lemma cyclic (S : StarSubalgebra ℂ (H →L[ℂ] H)) (T : H →L[ℂ] H)
    (hT : T ∈ Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H)))) (x : H) :
    T x ∈ closure {v | ∃ a ∈ S, v = a x} := by
  let K := (orbitSub S x).topologicalClosure
  have hK : ∀ a ∈ S, K ∈ Module.End.invtSubmodule a.toLinearMap := by
    intro a ha
    rw [Module.End.mem_invtSubmodule]
    intro y hy
    exact orbit_closure_invariant S x a ha hy
  have hx : x ∈ K := by
    apply Submodule.le_topologicalClosure
    exact ⟨1, S.one_mem, by simp⟩
  have h := (Module.End.mem_invtSubmodule _).mp (bicommutant_invariant S K hK hT) hx
  change T x ∈ closure (orbitSub S x : Set H) at h
  apply closure_mono _ h
  rintro y ⟨a, ha, eq⟩
  exact ⟨a, ha, eq.symm⟩

/-- **von Neumann double commutant theorem**: a unital star-subalgebra is WOT-closed if and only if it equals its bicommutant. The cyclic projection argument and finite amplification yield the forward direction; centralizers are WOT-closed for the reverse. -/
@[blueprint "VonNeumannDoubleCommutantTheorem.MainTheorem"]
theorem MainTheorem (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    IsClosed ((ContinuousLinearMap.toWOT (RingHom.id ℂ) H H) '' (S : Set (H →L[ℂ] H))) ↔
      Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))) = (S : Set (H →L[ℂ] H)) := by
  apply assembly S
  intro I T hT x
  exact cyclic _ _ hT x

end VonNeumannDoubleCommutantTheorem
