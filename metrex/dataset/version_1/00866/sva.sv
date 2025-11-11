// SVA for d_ff_reset_preset: synchronous active-low reset, active-low preset; reset has priority
module d_ff_reset_preset_sva (input logic clk, reset, preset, d, q);

  // Sample after NBA to avoid race with RTL nonblocking updates
  default clocking cb @(posedge clk);
    input #1step clk, reset, preset, d, q;
  endclocking

  // Functional truth table (priority: reset > preset > d)
  a_reset_dominates: assert property ( !reset |-> (q == 1'b0) );
  a_preset_active:   assert property (  reset && !preset |-> (q == 1'b1) );
  a_pass_d:          assert property (  reset &&  preset |-> (q == d)    );

  // Sanity: q should never be X/Z at the sampled time
  a_q_known:         assert property ( !$isunknown(q) );

  // Coverage of all cases
  c_reset:           cover  property ( !reset && (q == 1'b0) );
  c_preset:          cover  property (  reset && !preset && (q == 1'b1) );
  c_pass0:           cover  property (  reset &&  preset && (d == 1'b0) && (q == 1'b0) );
  c_pass1:           cover  property (  reset &&  preset && (d == 1'b1) && (q == 1'b1) );

endmodule

// Bind into the DUT
bind d_ff_reset_preset d_ff_reset_preset_sva sva_i (.*);