import CombinedRamsey.Revised20261018
import Lean.Util.CollectAxioms

/-! A fresh transitive audit for the supplied revision. The manuscript
inventory and scope clarification are recorded in the dated report. -/

#print axioms CombinedRamsey.Revised20261018.precompact_transfer
#print axioms CombinedRamsey.Revised20261018.precompact_transfer_exact_degree_one
#print axioms CombinedRamsey.Revised20261018.FiniteStage.finite_stage
#print axioms CombinedRamsey.Revised20261018.FiniteStage.degree_upper
#print axioms CombinedRamsey.Revised20261018.recoded_embedding_iff
#print axioms CombinedRamsey.Revised20261018.recoded_source_degree_one
#print axioms CombinedRamsey.Revised20261018.finite_added_symbols
#print axioms CombinedRamsey.Revised20261018.Positive.unrestricted_existence
#print axioms CombinedRamsey.Revised20261018.Positive.initial_palette_quantitative_bound
#print axioms CombinedRamsey.Positive.Marker.every_hypergraph_uniform_envelopes
#print axioms CombinedRamsey.Positive.conjecture47_pattern_false
#print axioms CombinedRamsey.Positive.Relational.new_chi_exact_minimum
#print axioms CombinedRamsey.Revised20261018.Negative.age_exact_literal
#print axioms CombinedRamsey.Revised20261018.Negative.actual_realization_age_formula
#print axioms CombinedRamsey.Revised20261018.Negative.negative_main
#print axioms CombinedRamsey.Revised20261018.Negative.containing_delta_infinite_degrees
#print axioms CombinedRamsey.Revised20261018.Negative.no_big_ramsey_structure
#print axioms CombinedRamsey.Revised20261018.Negative.no_singleton_degree_one_expansion

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let mut revisionDeclarations := 0
  let mut revisionTheorems := 0
  let mut projectTheorems := 0
  for (name, info) in env.constants.toList do
    let printable := name.toString
    let revision := (`CombinedRamsey.Revised20261018).isPrefixOf name ||
      printable.startsWith "_private.CombinedRamsey.Revised20261018."
    let project := (`CombinedRamsey).isPrefixOf name ||
      (`RelationalRamsey632).isPrefixOf name || (`Generic3Ramsey).isPrefixOf name ||
      printable.startsWith "_private.CombinedRamsey." ||
      printable.startsWith "_private.RelationalRamsey632." ||
      printable.startsWith "_private.Generic3Ramsey."
    if project then
      if revision then
        revisionDeclarations := revisionDeclarations + 1
        if info matches .thmInfo _ then
          revisionTheorems := revisionTheorems + 1
      if info matches .thmInfo _ then
        projectTheorems := projectTheorems + 1
      for axiomName in ← Lean.collectAxioms name do
        unless allowed.contains axiomName do
          throwError "Unapproved axiom {axiomName} in {name}"
  if revisionTheorems == 0 then
    throwError "No new-revision proof interface was loaded."
  logInfo m!"Revised20261018 audit passed: {revisionDeclarations} revision declarations, {revisionTheorems} revision theorems; {projectTheorems} total project theorems; only standard Lean axioms."
  logInfo "The supplied TeX hash and statement coverage are checked separately. The auxiliary Gsigma language is restricted to arities at least two; the general relational existence theorem permits unary symbols."
