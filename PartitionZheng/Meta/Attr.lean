/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public meta import Lean

/-!
# The `pz_tag` attribute

`@[pz_tag "TAG"]` marks a Lean declaration as a formalization of the result
named `TAG` in the source paper, and stores that name so the declarations
formalizing a given result can be recovered from the environment.

It is the analogue of Mathlib's `@[stacks TAG]`, with a single string parameter
rather than a source-and-tag pair, since all tags here name results of one
paper.

The tag goes on every declaration whose statements together make up the named
result, not merely on the first of them; declarations internal to a proof carry
no tag.
-/

public meta section

open Lean

/-- `@[pz_tag "TAG"]` attaches the tag `TAG`, a name of a result of the source
paper, to a declaration.

The syntax node is named `pzTag`, not `pz_tag`: the user-facing token keeps the
underscore, matching Mathlib's `@[stacks ...]`, but Mathlib's
`defsWithUnderscore` linter inspects the declaration name, so the internal name
must be lowerCamelCase. -/
syntax (name := pzTag) "pz_tag " str : attr

/-- Links a Lean declaration to the name of the result it formalizes. -/
initialize pzTagAttr : ParametricAttribute String ←
  registerParametricAttribute {
    name := `pzTag
    descr := "Links a Lean declaration to the name of the result it formalizes."
    getParam := fun _ stx => do
      match stx with
      | `(attr| pz_tag $s:str) => return s.getString
      | _ => throwError "pz_tag takes exactly one string literal, the result's tag"
  }
