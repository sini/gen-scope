# Drafted amendment: fix `unrun` as a verbatim pass-through at the minting entry

**Status of this file.** A draft handed to the orchestrator, who lands it papers-side. It is not a
papers edit and nothing here has been written to the papers repository. It lives in the `gen-scope`
worktree because that is where the cells that depend on it live; it is deleted or relocated by
whoever lands it.

## Why an amendment rather than a cell change

Five cells in `ci/tests-pending.nix` observe values that the minting instance computes **before its
driver runs** — the derived schedule, the per-stratum `emitted`, the per-stratum `settled`, and
`advance`'s formal set. None of those appear in the entry's `Result`, which carries `nodes`, `edges`,
`strata` and `unrun` only, and `strata` is an `Int`. The cells reach them by substituting the
module's `stratify` formal with a driver that reports instead of walking, and returning the report
through `unrun` — **the only field on the specified result surface that originates in the driver and
is carried rather than derived.**

A **sixth** cell depends on the same guarantee by a different route: the arming for the emptiness
theorem substitutes a driver whose schedule omits the last declared stratum and asserts that the
entry reports the resulting leftovers **non-empty**. That is the real driver's own `unrun`, not a
spy's payload, and a constant empty list breaks it too.

★ **The seventh cell that touches the field does NOT depend on it, and that asymmetry is the whole
argument.** `unrun == [ ]` on every fixture is satisfied by an entry that returns a constant empty
list. So the cell that looks like the field's subject is exactly the one that cannot detect the
implementation this amendment forbids — the commitment is invisible to the assertion it most
resembles, which is why it has to be stated in the rules rather than left to be inferred from them.

That readout works only if the entry returns the driver's `unrun` **unexamined**. The rules as
written do not say so:

- R§2.6's `Result` block annotates `unrun` as *"EMPTY by R§4.1.1 + R§4.1; carried because the
  driver's Result carries it"* — `carried` is suggestive but not normative about identity.
- R§4.2 says, in the other direction, that `unrun` *"is not a live channel here"* and that **"no
  mitigation in this document may rest on a consumer reading it."**

Read together, an implementer building the entry may reasonably write `unrun = [ ];` as a constant —
it satisfies the annotation's *value* claim on every conformant fixture and honours R§4.2's warning
about depending on the field. Under that implementation the six cells go **permanently red**, and
they go red inside assertion text that the relocation item forbids rewriting. The failure would
surface as a red suite at the green-after gate with no defect in either the entry or the cells.

The partition is measured, not asserted: over the 34 declared cells, **6 depend** on the
pass-through, **1 reads `unrun` and does not depend** on it (the theorem), and **27 do not touch the
field**.

The commitment is **unavoidable, not chosen**: the specified result surface offers no other channel,
and the values are ones the phase's own oracle requires observing. So it belongs in the rules.

## The sentence, and where it inserts

**Insert into R§2.6, as a new paragraph immediately after the `★ Why the frozen set is absent from
`Args` and a stratum-0 seed is refused.` paragraph** (i.e. as the clause's final paragraph, before
the `---` that closes the section):

> ★ **`unrun` is the driver's `unrun` VERBATIM, and the pass-through is contractual rather than
> incidental.** `mintStrata` returns the list its driver returned, unexamined and untransformed — it
> does not filter it, does not re-type it, and does not substitute a constant for it. On every
> conformant run that list is empty by theorem (R§4.1.1 + R§4.1), so the guarantee is invisible in
> production and costs the entry nothing; what it buys is that a **substituted driver's** result is
> observable at the entry, which is the only channel by which the values the instance computes
> before its driver runs — the derived `schedule`, `advance`'s per-stratum `emitted` and `settled`,
> and `advance`'s own formal set — are reachable by a cell at all. **This does not reopen R§4.2's
> prohibition:** that clause forbids a *mitigation* resting on a consumer reading `unrun`, and no
> mitigation does; identity of the carried value is a statement about what the entry may do to a
> field, not a behaviour anyone depends on in a conformant run.

## What the amendment does not do

It does not make `unrun` non-empty in any conformant run, does not give it a consumer, and does not
weaken R§4.2 — under R§4.1.1 the emitter set is fixed and the schedule is derived from it, so the
theorem that produces `unrun == [ ]` is untouched. It constrains exactly one thing: the entry may not
*replace* the driver's list.

## Consumers, if the clause's CONSUMERS line is updated with it

R§6.1's arms are unaffected. The affected work item is the cell set, whose schedule-derivation,
emission, settled-arming and `advance`-record cells all read through this channel.
