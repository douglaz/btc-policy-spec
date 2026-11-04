# Hot accounting: commitment-keyed versus transaction-keyed

Research task `bps-uaer.15`, base `64eb65c`. No protocol rule changes and no decision: `F63` stays
open and `BtcPolicy.Ledger.current` is unchanged. Adopting any other accounting is a protocol change
that needs an owner decision.

**What is compared.** The current ledger, `BtcPolicy.Ledger`, keeps one row per commitment. The
candidate, `BtcPolicy.TxAccounting`, keeps one row per txid, as `F63`'s first direction sketches: "its
exposure the OR over the commitments that name it". The candidate is no guard value and carries no
requirement tag. Three choices `F63` leaves open are this model's own: a row keeps one entry per
commitment, each with its own reservation time and expiry, and the charge lasts until the last entry
is released; a row remembers every commitment that named it; the capacity of 4 096 counts entries.
Both ledgers step over the same `Kernel.step`, and each exhibit below runs through the composed step
under `Ledger.current` and `Kernel.current`. Exhibits are in `BtcPolicy.Exhibits.TxAccounting`; other
unprefixed names are in `BtcPolicy.TxAccounting`.

**Result.** Neither accounting dominates (`neither_accounting_dominates`). The candidate admits a
re-quote the current ledger refuses, and the current ledger admits a distinct spend the candidate
refuses, because the candidate keeps an exposed transaction charged longer. With one commitment per
transaction the two are the same system.

## The eight cases

| Case | Current ledger | Candidate | Relation | Declarations |
| --- | --- | --- | --- | --- |
| Exact retry | Nothing moves; original time and amount | The same | Same | `retry_changes_nothing`, `exact_retry_preserved` |
| New expiry over one transaction | A second full charge; a maximal spend's re-quote is refused inside its window | No new charge, one more entry; admitted below the entry capacity | Strict difference | `requote_adds_no_charge`, `requote_admitted`, `requote_refused_at_capacity`, `requote_of_maximal_spend` |
| Distinct RBF transaction | Its own full charge, over the same input | The same | Same | `distinct_keeps_own_charge`, `distinct_admitted_iff`, `reserve_leaves_other_rows`, `rbf_keeps_its_own_charge` |
| One exposed twin | Each row has its own bit: the unexposed twin is refunded, and the node can charge nothing while its partial is out | The bit is the row's, and no prune pass refunds the row | Strict difference | `exposed_never_refunded`, `exposed_twin_blocks_the_refund` |
| All commitments expire | Row by row: unexposed, expiry strictly past on the wall, candidate gone (`Ledger.prune_refunds_only_unexposed_and_expired`) | All at once: unexposed, every standing entry strictly past, no named candidate resident (`refund_iff`) | Same end on the exhibited history, different path: `2V`, `V`, `0` against `V`, `V`, `0` | `settlement_refunds_nothing`, `unexposed_twins_refund` |
| Aged-out exposed authority | The release ignores exposure; quorum outlives the charge | The same | Same conclusion | `release_ignores_exposure`, `tsysStep_exposure`, `nonhot_step_is_kernel`, `aged_out_authority_outlives_both`, `requote_after_release_forgets_exposure` |
| Backward clocks | One way (`Ledger.released_never_due`) | One way, per entry and per row | Same closure | `released_stays_gone`, `entry_released_below_ratchet`, `entry_released_never_due`, `uncharged_fire_closed_under_candidate`, `released_stays_out_under_backward_wall` |
| Normal and duress worlds | Coupled inside the horizon (`Silence.silence`) | Coupled inside the horizon, for ledger, budget verdict and effects | Same inside; past it both split, not always alike | `t_coupled_walk`, `tRefused_pin`, `coupled_premises`, `coupled_walks_inhabited`, `past_horizon_split` |

## Established equivalences

`same_steps_without_twins`: under `hs : g.settlement = .retainOnMempool`,
`hr : g.release = .acceptedAdmission` and `hrf : g.refund = .onCollection`, from a ledger with
`OneToOne name`, over a trace with `Names name` on every step (each accepted spend's commitment id is
`name` of its txid), the candidate's state projects to the current ledger's and the effects are equal.
No premise is taken on the samples. `adr0014_same_under_candidate` applies it to `ADR-0014`'s trace;
`twins_break_the_projection` is the failing sibling.

`tSum_le_cap`: for every finite trace, a ledger under the cap stays under it, with no other premise.

`t_bridge`: `q * Ledgers.outflow cohort ≤ cuts.length * cfg.cap`, `Ledger.bridge`'s conclusion, with
its premises read over txids: `hnd`, `hamt`, `hinv`, `hcohort`, all taken as given at the cuts.
`bridge_nonvacuous` is one reachable instance, where a re-quoted transaction is one cohort member.

`tSum_le_proj`: over one set of rows, each holding an entry, the candidate's sum is at or below the
current ledger's. It compares one row set only. The next section's histories reach different row sets.

## Strict differences and counterexamples

- **Better under the candidate.** `POL-17` says "equality meaning one maximal spend may consume the
  whole window", and under the current ledger such a spend cannot be re-quoted inside it
  (`requote_of_maximal_spend`). With room for both commitments, the second charge also blocks a distinct
  spend the candidate admits (`requote_frees_budget`).
- **Worse under the candidate.** A re-quote keeps the charge standing: at 200 a distinct spend is refused,
  where the current ledger, having refused the re-quotes, admits it (`requote_holds_the_charge_longer`).
  An exposed twin keeps its row past the prune pass that clears the current ledger's, and the next
  distinct spend is refused there (`exposed_twin_blocks_the_refund`).
- **A simplification that fails.** Keeping only the first reservation time drops a charge the twin's own
  window holds (`first_time_only_loses_charge`).
- **Not a repair of completion.** `POL-20` says "Already exposed signatures also remain valid after their
  reservations age out", and both accountings show it (`aged_out_authority_outlives_both`). Neither
  bounds later completion, and a re-quote after the row has gone starts unexposed under both
  (`requote_after_release_forgets_exposure`).

## Preservation obligations if the candidate were adopted

`F63`'s bar for a fix, checked here:

| Bar | Evidence |
| --- | --- |
| Nothing netted across distinct transactions | `distinct_keeps_own_charge`, `distinct_admitted_iff`, `rbf_keeps_its_own_charge` |
| The outpoint set not a lookup key | `tReserve` reads `c.tx.id` and no input; `rbf_keeps_its_own_charge` gives one input two rows |
| The bridge's `hcap` provable by induction | `tSum_le_cap`, `t_bridge` |
| A re-quote's verdict independent of the PIN | `tRefused_pin`, `t_coupled_walk` |

Further obligations this comparison found: a txid that binds the outflow, since a row keeps its first
amount (`txid_must_bind_outflow`); a capacity over entries, since rows no longer bound re-quotes
(`requote_refused_at_capacity`); and per-entry reservation times (`first_time_only_loses_charge`).

## Unresolved

- **`hamt` and `hcohort` over a candidate run.** `Admission.fed_bridge` derives them for the current
  ledger. No candidate version exists: `t_bridge` takes them as given. Nothing here shows the derivation
  fails. It was not attempted for a candidate nobody has adopted.
- **The observation walk.** `Silence.obsOf` reads `Ledger.Sys`, so `Silence.silence` is not restated for
  the candidate. `t_coupled_walk` proves the coupling, verdicts and effects only.
- **Past the horizon.** Both accountings split the two worlds there, on one commitment
  (`past_horizon_split`), and with a re-quote the same schedule splits the candidate's rows and not the
  current ledger's. That exhibit's runs hold no Lockdown, and whether such a split can be observed before
  Lockdown is not established for either accounting.
- **`NCH-24`'s lookup eviction** is modelled under neither accounting.
- **Retained names.** `tReserve` appends to a row's `named` and `tAgeOut` never shrinks it, so a row kept
  standing by re-quotes grows past what `entryCount` bounds. No bound on it is modelled.
- **Exposure after the row has gone.** Reading the world's exposure rather than the row's commitments is
  not modelled, and neither is its effect on budget verdicts.

## The decision this leaves

`F63` stays open with its two directions, and the comparison does not choose. Keeping the commitment as
the unit still needs its unit stated and `ADR-0014`'s sentence split. Adopting the transaction as the unit
trades the strict differences above and takes on the obligations above. Either way the text changes are
an owner decision.
