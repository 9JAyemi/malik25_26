// SVA for sync_r2w (concise, quality-focused)
// Bind these directly; they cover reset behavior, 2-flop shift semantics, and propagation.
// Note: wq1_rptr is internal; direct bind lets us check it without extra ports.

bind sync_r2w
  // While in reset, both sync stages must be 0
  assert property (@(posedge wclk)
                   !wrst_n |-> ({wq2_rptr,wq1_rptr} == '0))
    else $error("sync_r2w: stages not 0 during reset");

bind sync_r2w
  // On first wclk after reset deassert, wq2_rptr still 0 (since previous wq1_rptr was 0)
  assert property (@(posedge wclk)
                   $rose(wrst_n) |-> (wq2_rptr == '0))
    else $error("sync_r2w: wq2_rptr not 0 on reset release");

bind sync_r2w
  // Core 2-flop shift behavior: {wq2,wq1} <= {wq1,rptr}
  assert property (@(posedge wclk) disable iff (!wrst_n)
                   {wq2_rptr,wq1_rptr} == {$past(wq1_rptr), $past(rptr)})
    else $error("sync_r2w: shift relation violated");

bind sync_r2w
  // Equivalent end-to-end check: wq2 is rptr delayed by 2 cycles (after 2 clean cycles out of reset)
  assert property (@(posedge wclk) disable iff (!wrst_n)
                   $past(wrst_n,2) |-> (wq2_rptr == $past(rptr,2)))
    else $error("sync_r2w: 2-cycle latency from rptr to wq2_rptr violated");

bind sync_r2w
  // No X/Z on synchronized stages when out of reset
  assert property (@(posedge wclk) disable iff (!wrst_n)
                   !$isunknown({wq2_rptr,wq1_rptr}))
    else $error("sync_r2w: X/Z detected on sync stages");

// Coverage

bind sync_r2w
  // Exercise reset assert/deassert
  cover property (@(posedge wclk) $fell(wrst_n) ##[1:$] $rose(wrst_n));

bind sync_r2w
  // Observe a change on rptr propagating to wq2_rptr two cycles later
  cover property (@(posedge wclk) disable iff (!wrst_n)
                  $changed(rptr) ##2 (wq2_rptr == $past(rptr,2)));

bind sync_r2w
  // See at least one non-zero value make it through to wq2_rptr
  cover property (@(posedge wclk) disable iff (!wrst_n)
                  (wq2_rptr != '0));