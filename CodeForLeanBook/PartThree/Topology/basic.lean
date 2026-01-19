import Mathlib

#check TopologicalSpace

#check IsOpen

#check isClosed_compl_iff

#check Dense

#check interior

#check closure

#check IsCompact

#check isCompact_iff_finite_subcover

section metric

variable {X : Type*} [MetricSpace X]

#synth TopologicalSpace X

#check Metric.isOpen_iff

end metric

section subtype_topology

variable {X : Type*} [TopologicalSpace X] (S : Set X)

#synth TopologicalSpace S

#check isOpen_induced_iff



end subtype_topology

section prod_topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

#synth TopologicalSpace (X × Y)
#check isOpen_prod_iff
#check isOpen_coinduced

end prod_topology

section order

variable {X : Type*}

#synth CompleteLattice (TopologicalSpace X)

-- discrete topology
#check (⊥ : TopologicalSpace X)

-- indiscrete topology
#check (⊤ : TopologicalSpace X)


end order

section quotient

variable {X : Type*} [TopologicalSpace X] (s : Setoid X)

#synth TopologicalSpace (Quotient s)

end quotient
