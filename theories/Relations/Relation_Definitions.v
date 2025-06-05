From Corelib Require Export RelationClasses.
From Corelib Require Import Relation_Definitions.

Notation relation := relation (only parsing).

#[deprecated(since="9.1", use=Reflexive)]
Notation reflexive := reflexive (only parsing).
#[deprecated(since="9.1", use=Transitive)]
Notation transitive := transitive (only parsing).
#[deprecated(since="9.1", use=Symmetric)]
Notation symmetric := symmetric (only parsing).
#[deprecated(since="9.1", use=Antisymmetric)]
Notation antisymmetric := antisymmetric (only parsing).
#[deprecated(since="9.1", use=Equivalence)]
Notation equiv := equiv (only parsing).
#[deprecated(since="9.1", use=PreOrder)]
Notation preorder := preorder (only parsing).
#[deprecated(since="9.1", use=Build_PreOrder)]
Notation Build_preorder := Build_preorder (only parsing).
#[deprecated(since="9.1", use=PreOrder_Reflexive)]
Notation preord_refl := preord_refl (only parsing).
#[deprecated(since="9.1", use=PreOrder_Transitive)]
Notation preord_trans := preord_trans (only parsing).
#[deprecated(since="9.1", use=PartialOrder)]
Notation order := order (only parsing).
#[deprecated(since="9.1", note="Use RelationClasses.PartialOrder")]
Notation Build_order := Build_order (only parsing).
#[deprecated(since="9.1", use=partial_order_antisym)]
Notation ord_antisym := ord_antisym (only parsing).
#[deprecated(since="9.1", note="Use RelationClasses.PartialOrder")]
Notation ord_refl := ord_refl (only parsing).
#[deprecated(since="9.1", note="Use RelationClasses.PartialOrder")]
Notation ord_trans := ord_trans (only parsing).
#[deprecated(since="9.1", use=Equivalence)]
Notation equivalence := equivalence (only parsing).
#[deprecated(since="9.1", use=Build_Equivalence)]
Notation Build_equivalence := Build_equivalence (only parsing).
#[deprecated(since="9.1", use=Equivalence_Reflexive)]
Notation equiv_refl := equiv_refl (only parsing).
#[deprecated(since="9.1", use=Equivalence_Transitive)]
Notation equiv_trans := equiv_trans (only parsing).
#[deprecated(since="9.1", use=Equivalence_Symmetric)]
Notation equiv_sym := equiv_sym (only parsing).
#[deprecated(since="9.1", use=RelationClasses.PER)]
Notation PER := PER (only parsing).
#[deprecated(since="9.1", use=RelationClasses.Build_PER)]
Notation Build_PER := Build_PER (only parsing).
#[deprecated(since="9.1", use=RelationClasses.PER_Symmetric)]
Notation per_sym := per_sym (only parsing).
#[deprecated(since="9.1", use=RelationClasses.PER_Transitive)]
Notation per_trans := per_trans (only parsing).
#[deprecated(since="9.1", use=subrelation)]
Notation inclusion := inclusion (only parsing).
#[deprecated(since="9.1", use=relation_equivalence)]
Notation same_relation := same_relation (only parsing).
#[deprecated(since="9.1", note="If you would like the standard library to keep this definition, please open an issue")]
Notation commut := commut (only parsing).
