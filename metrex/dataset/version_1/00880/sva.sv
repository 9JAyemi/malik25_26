// SVA for top_module
module top_module_sva (
  input logic clk,
  input logic reset,
  input logic a,
  input logic b,
  input logic sel_b1,
  input logic q,
  input logic mux_out,
  input logic flip_flop_out,
  input logic final_out
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Past-valid guard for $past usage
  logic past_valid;
  always_ff @(posedge clk or posedge reset) begin
    if (reset) past_valid <= 1'b0;
    else       past_valid <= 1'b1;
  end

  // 2:1 mux correctness
  ap_mux_sel0: assert property (sel_b1==1'b0 |-> mux_out==a);
  ap_mux_sel1: assert property (sel_b1==1'b1 |-> mux_out==b);

  // DFF: out is previous cycle's mux_out
  ap_ff_sample: assert property (past_valid |-> flip_flop_out == $past(mux_out));

  // functional_module: 1-bit add == XOR
  ap_func_xor: assert property (final_out == (mux_out ^ flip_flop_out));

  // Output connectivity
  ap_q_conn: assert property (q == final_out);

  // End-to-end behavior: q == mux_out ^ $past(mux_out)
  ap_q_eq_toggle: assert property (past_valid |-> q == (mux_out ^ $past(mux_out)));

  // Sanity on q vs mux_out stability
  ap_q_zero_when_stable: assert property (past_valid && mux_out==$past(mux_out) |-> q==1'b0);
  ap_q_one_when_change:  assert property (past_valid && mux_out!=$past(mux_out) |-> q==1'b1);

  // Coverage

  // Exercise both mux paths with toggling data
  cv_mux_path_a_toggle: cover property (past_valid && sel_b1==1'b0 && $changed(a) && mux_out==a);
  cv_mux_path_b_toggle: cover property (past_valid && sel_b1==1'b1 && $changed(b) && mux_out==b);

  // FF captures both 0->1 and 1->0
  cv_ff_rise: cover property (past_valid && $rose(flip_flop_out));
  cv_ff_fall: cover property (past_valid && $fell(flip_flop_out));

  // functional_module truth table
  cv_func_00: cover property (mux_out==1'b0 && flip_flop_out==1'b0 && final_out==1'b0);
  cv_func_10: cover property (mux_out==1'b1 && flip_flop_out==1'b0 && final_out==1'b1);
  cv_func_01: cover property (mux_out==1'b0 && flip_flop_out==1'b1 && final_out==1'b1);
  cv_func_11: cover property (mux_out==1'b1 && flip_flop_out==1'b1 && final_out==1'b0);

  // End-to-end q activity
  cv_q_pulse1: cover property (past_valid && $changed(mux_out) && q==1'b1);
  cv_q_low_stable: cover property (past_valid && !$changed(mux_out) && q==1'b0);

endmodule

// Bind into DUT
bind top_module top_module_sva u_top_module_sva (
  .clk(clk),
  .reset(reset),
  .a(a),
  .b(b),
  .sel_b1(sel_b1),
  .q(q),
  .mux_out(mux_out),
  .flip_flop_out(flip_flop_out),
  .final_out(final_out)
);