// SVA for oh_reg1
// Bind this module to the DUT:
// bind oh_reg1 oh_reg1_sva #(.DW(DW)) u_oh_reg1_sva (.*,.out_reg(out_reg));

module oh_reg1_sva #(parameter int DW=1)
(
  input             clk,
  input             nreset,
  input             en,
  input  [DW-1:0]   in,
  input  [DW-1:0]   out,
  input  [DW-1:0]   out_reg
);

  // Basic sanity on parameter
  initial assert (DW >= 1) else $error("DW must be >= 1");

  // Default synchronous clock
  default clocking cb @(posedge clk); endclocking

  // Reset drives zero on every sampled cycle while asserted
  a_reset_forces_zero: assert property (@(cb) !nreset |-> out == '0);

  // Async reset must clear output no later than the next posedge clk
  a_async_clear_fast:  assert property (@(posedge clk or negedge nreset)
                                        $fell(nreset) |-> ##[0:1] (out == '0));

  // Load-enable behavior
  a_load_when_en:      assert property (@(cb) disable iff (!nreset)
                                        en |-> out == $past(in));

  // Hold behavior when not enabled
  a_hold_when_dis:     assert property (@(cb) disable iff (!nreset)
                                        !en |-> out == $past(out));

  // Output must not be X/Z while out of reset
  a_no_unknown_out:    assert property (@(cb) nreset |-> !$isunknown(out));

  // Structural consistency: continuous assign matches internal reg
  a_out_matches_reg:   assert property (@(cb) out == out_reg);

  // Coverage
  c_reset_cycle:       cover property (@(cb) $fell(nreset) ##[1:10] $rose(nreset));
  c_load:              cover property (@(cb) disable iff (!nreset)
                                        en ##1 (out == $past(in)));
  c_hold:              cover property (@(cb) disable iff (!nreset)
                                        !en ##1 $stable(out));
  c_two_distinct_loads: cover property (@(cb) disable iff (!nreset)
                                        en ##1 (out == $past(in)) ##1
                                        en && (in != $past(out)));

endmodule