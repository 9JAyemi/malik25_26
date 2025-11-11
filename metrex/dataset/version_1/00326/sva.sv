// SystemVerilog Assertions for the provided design
// Concise, high-signal-coverage, focusing on functional checks and useful coverage

// ---------------- bmu ----------------
module bmu_sva (
  input        cx0, cx1,
  input  [1:0] bm0, bm1, bm2, bm3, bm4, bm5, bm6, bm7
);
  // Combinational correctness + consistency
  always @* begin
    assert (bm0 == (cx0 ? 2'b00 : 2'b11)) else $error("bmu: bm0 mismatch");
    assert (bm1 == (cx0 ? 2'b01 : 2'b10)) else $error("bmu: bm1 mismatch");
    assert (bm2 == (cx1 ? 2'b00 : 2'b11)) else $error("bmu: bm2 mismatch");
    assert (bm3 == (cx1 ? 2'b01 : 2'b10)) else $error("bmu: bm3 mismatch");
    assert (bm4 == (cx1 ? 2'b00 : 2'b11)) else $error("bmu: bm4 mismatch");
    assert (bm5 == (cx1 ? 2'b01 : 2'b10)) else $error("bmu: bm5 mismatch");
    assert (bm6 == (cx1 ? 2'b00 : 2'b11)) else $error("bmu: bm6 mismatch");
    assert (bm7 == (cx1 ? 2'b10 : 2'b01)) else $error("bmu: bm7 mismatch");
    // Redundancy/consistency relations
    assert (bm2 == bm4 && bm4 == bm6) else $error("bmu: bm2/bm4/bm6 not equal");
    assert (bm3 == bm5) else $error("bmu: bm3!=bm5");
    // Simple stimulus coverage
    cover (cx0==0); cover (cx0==1);
    cover (cx1==0); cover (cx1==1);
  end
endmodule
bind bmu bmu_sva bmu_sva_i (
  .cx0(cx0), .cx1(cx1),
  .bm0(bm0), .bm1(bm1), .bm2(bm2), .bm3(bm3), .bm4(bm4), .bm5(bm5), .bm6(bm6), .bm7(bm7)
);

// ---------------- add_compare_select_3 ----------------
// Check both: the as-coded condition semantics and width truncation on d
module add_compare_select_3_sva (
  input  [3:0] npm,
  input        d,
  input  [3:0] pm1, pm2,
  input  [1:0] bm1, bm2
);
  logic cond;
  always @* begin
    // Equality has higher precedence than &: this reproduces RTL meaning
    cond = ((npm[3] == bm1[1]) & (npm[2:0] == {2'b00, bm1[0]}));
    assert (d === (cond ? pm1[0] : pm2[0])) else $error("acs3: select/LSB mismatch");
    cover (cond); cover (!cond);
  end
endmodule
bind add_compare_select_3 add_compare_select_3_sva acs3_sva_i (.*);

// ---------------- add_compare_select_2 ----------------
module add_compare_select_2_sva (
  input  [3:0] npm,
  input        d,
  input  [3:0] pm1, pm2,
  input  [1:0] bm1, bm2
);
  logic cond;
  always @* begin
    // As-coded zero-extend RHS: compare npm[3:1] to {1'b0, bm1[1], bm1[0]}
    cond = (npm[3:1] == {1'b0, bm1[1], bm1[0]});
    assert (d === (cond ? pm1[0] : pm2[0])) else $error("acs2: select/LSB mismatch");
    cover (cond); cover (!cond);
  end
endmodule
bind add_compare_select_2 add_compare_select_2_sva acs2_sva_i (.*);

// ---------------- add_compare_select_1 ----------------
module add_compare_select_1_sva (
  input  [3:0] npm,
  input        d,
  input  [3:0] pm1, pm2,
  input  [1:0] bm1, bm2
);
  logic cond;
  always @* begin
    cond = (npm[3] == bm1[1]);
    assert (d === (cond ? pm1[0] : pm2[0])) else $error("acs1: select/LSB mismatch");
    cover (cond); cover (!cond);
  end
endmodule
bind add_compare_select_1 add_compare_select_1_sva acs1_sva_i (.*);

// ---------------- add_compare_select_0 ----------------
module add_compare_select_0_sva (
  input  [3:0] npm,
  input        d,
  input  [3:0] pm1, pm2,
  input  [1:0] bm1, bm2
);
  always @* begin
    assert (d === pm1[0]) else $error("acs0: LSB mismatch");
    cover (pm1[0]==0); cover (pm1[0]==1);
  end
endmodule
bind add_compare_select_0 add_compare_select_0_sva acs0_sva_i (.*);

// ---------------- pmsm ----------------
module pmsm_sva (
  input  [3:0] npm0, npm1, npm2, npm3,
  input  [3:0] pm0,  pm1,  pm2,  pm3,
  input        clk, reset
);
  default clocking cb @(posedge clk); endclocking
  // Async reset drives zeros
  a_reset_zero: assert property (reset |-> (pm0==4'b0 && pm1==4'b0 && pm2==4'b0 && pm3==4'b0))
    else $error("pmsm: reset not zeroing outputs");
  // Register update (one-cycle transfer)
  a_update: assert property (!reset && !$past(reset) |-> {pm0,pm1,pm2,pm3} == $past({npm0,npm1,npm2,npm3}))
    else $error("pmsm: outputs not following inputs with 1-cycle latency");
  // Coverage: see any change in stored metrics (helps catch unintended lock-up)
  c_pm_change: cover property (!reset && $changed({pm0,pm1,pm2,pm3}));
endmodule
bind pmsm pmsm_sva pmsm_sva_i (.*);

// ---------------- spd ----------------
module spd_sva (
  input        d0, d1, d2, d3,
  input  [3:0] pm0, pm1, pm2, pm3,
  input        out, clk, reset,
  // Internal state visibility via bind
  input  [3:0] pm_reg,
  input        out_reg
);
  default clocking cb @(posedge clk); endclocking

  // Combinational tie-off correctness
  always @* begin
    assert (out === out_reg) else $error("spd: out != out_reg");
  end

  // Reset behavior
  a_spd_reset: assert property (reset |-> (pm_reg==4'b0 && out==1'b0))
    else $error("spd: reset not clearing state");

  // Shift register update
  a_shift: assert property (!reset && !$past(reset) |-> pm_reg == { $past(pm_reg[2:0]), $past(out_reg) })
    else $error("spd: pm_reg shift mismatch");

  // Output decision uses previous pm_reg vs pm0
  a_out_sel: assert property (!reset && !$past(reset) |-> out == ($past(pm_reg) == $past(pm0)))
    else $error("spd: out comparator mismatch");

  // Coverage: observe both out values and a toggle
  c_out0: cover property (!reset && out==0);
  c_out1: cover property (!reset && out==1);
  c_out_toggle01: cover property (!reset && $fell(out));
  c_out_toggle10: cover property (!reset && $rose(out));
endmodule
bind spd spd_sva spd_sva_i (.*);

// ---------------- Top-level integration coverage (optional, light) ----------------
module viterbi_decoder_sva (
  input [1:0] cx,
  input       d,
  input       clk, reset
);
  default clocking cb @(posedge clk); endclocking
  // Stimulus coverage on inputs and observable output
  c_cx_change: cover property (!reset && $changed(cx));
  c_d_seen0:   cover property (!reset && d==0);
  c_d_seen1:   cover property (!reset && d==1);
endmodule
bind viterbi_decoder viterbi_decoder_sva vdec_sva_i (.*);