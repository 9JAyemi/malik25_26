// Place inside FIFO_image_filter_img_4_cols_V_shiftReg, before endmodule.
// Requires SystemVerilog (SVA). Guarded to avoid synthesis impact.
`ifdef ASSERT_ON

// Clocking and $past guard
default clocking cb @(posedge clk); endclocking
int unsigned cyc = 0;
always @(posedge clk) cyc <= cyc + 1;
default disable iff (cyc == 0);

// Basic sanity: known control/addr and in-range address
assert property (!$isunknown(ce)) else $error("ce is X/Z");
assert property (!$isunknown(a))  else $error("a is X/Z");
assert property (!$isunknown(a) |-> a < DEPTH)
  else $error("Address a out of range: %0d >= %0d", a, DEPTH);

// Output mux correctness
assert property (q == SRL_SIG[a]) else $error("q != SRL_SIG[a]");

// Hold behavior (no CE): all stages stable
genvar gi;
generate
  for (gi = 0; gi < DEPTH; gi++) begin : g_hold
    assert property (!ce |-> $stable(SRL_SIG[gi]))
      else $error("Stage %0d changed while ce==0", gi);
  end
endgenerate

// Shift behavior (CE): new data into stage 0, ripple forward
assert property (ce |-> SRL_SIG[0] == $past(data))
  else $error("Stage 0 not loaded with previous data when ce==1");

generate
  for (gi = 0; gi < DEPTH-1; gi++) begin : g_shift
    assert property (ce |-> SRL_SIG[gi+1] == $past(SRL_SIG[gi]))
      else $error("Stage %0d not loaded from stage %0d when ce==1", gi+1, gi);
  end
endgenerate

// End-to-end: after k+1 consecutive CE cycles, tap k holds data from k+1 cycles ago
generate
  genvar k;
  for (k = 0; k < DEPTH; k++) begin : g_e2e
    sequence ce_run_k; ce [* (k+1)]; endsequence
    assert property (disable iff (cyc <= k)
                     ce_run_k ##0 (a == k) |-> q == $past(data, k+1))
      else $error("Tap %0d mismatch: q != data delayed %0d cycles", k, k+1);
    // Coverage: hit each tap after a full CE run
    cover property (ce_run_k ##0 (a == k));
  end
endgenerate

// Coverage: CE toggling and all address values exercised
cover property (ce ##1 !ce ##1 ce);
generate
  for (gi = 0; gi < DEPTH; gi++) begin : g_addr_cov
    cover property (a == gi);
  end
endgenerate

`endif