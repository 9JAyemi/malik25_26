// SVA for sel_add
// Bind these assertions to the DUT and sample on any convenient free-running TB clock.

module sel_add_sva #(parameter W=4) (
  input  logic              clk,
  input  logic              rst_n,
  input  logic [W-1:0]      A,
  input  logic [W-1:0]      B,
  input  logic              SEL,
  input  logic              ADD,
  input  logic [W-1:0]      OUT
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // Basic sanity: no X/Z on inputs, and no X/Z on OUT when inputs are clean
  a_no_x_inputs:        assert property (!$isunknown({SEL, ADD, A, B}));
  a_no_x_out_when_ok:   assert property (!$isunknown({SEL, ADD, A, B}) |-> !$isunknown(OUT));

  // Functional equivalence (covers all three behaviors concisely)
  a_functional: assert property (
    OUT == (SEL ? (ADD ? (A + B)[W-1:0] : B) : A)
  );

  // Mode coverage
  c_sel0:        cover property (SEL == 1'b0);
  c_sel1_add0:   cover property (SEL && !ADD);
  c_sel1_add1:   cover property (SEL &&  ADD);

  // Addition overflow coverage (verifies truncation scenario occurs)
  c_overflow:    cover property (SEL && ADD && ((A + B) > {W{1'b1}}));

  // Simple mode-walk coverage (exercise all paths over time)
  c_mode_walk:   cover property ((SEL==0) ##1 (SEL && !ADD) ##1 (SEL && ADD));

endmodule

// Example bind (replace tb_clk/tb_rst_n with your TB clock/reset)
// bind sel_add sel_add_sva #(.W(4)) u_sel_add_sva ( .clk(tb_clk), .rst_n(tb_rst_n), .A(A), .B(B), .SEL(SEL), .ADD(ADD), .OUT(OUT) );