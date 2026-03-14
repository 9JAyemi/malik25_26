module BOR_sva (
  input logic Vin,
  input logic Vth,
  input logic clk,
  input logic reset,
  input logic rst_out,
  input logic bor_ff
);

  // rst_out is 0 during active-low reset.
  check_reset_forces_rst_out_low: assert property (
    @(posedge clk) !reset |-> (rst_out == 1'b0)
  );

  // bor_ff is 0 during active-low reset.
  check_reset_clears_bor_ff: assert property (
    @(posedge clk) !reset |-> (bor_ff == 1'b0)
  );

  // rst_out mirrors internal bor_ff.
  check_rst_out_mirrors_bor_ff: assert property (
    @(posedge clk) disable iff (!reset) (rst_out == bor_ff)
  );

  // With reset high in consecutive cycles, rst_out equals prior-cycle (Vin < Vth).
  check_registered_comparator_mapping: assert property (
    @(posedge clk) disable iff (!reset) $past(reset) |-> (rst_out == $past(Vin < Vth))
  );

  // If prior-cycle (Vin < Vth) was true, rst_out is 1 now.
  check_prev_comp_true_sets_out: assert property (
    @(posedge clk) disable iff (!reset) ($past(reset) && $past(Vin < Vth)) |-> (rst_out == 1'b1)
  );

  // If prior-cycle (Vin < Vth) was false, rst_out is 0 now.
  check_prev_comp_false_clears_out: assert property (
    @(posedge clk) disable iff (!reset) ($past(reset) && !$past(Vin < Vth)) |-> (rst_out == 1'b0)
  );

  // A rising edge on rst_out matches a 0->1 transition of (Vin < Vth) in the prior cycle.
  check_out_rise_matches_comp_rise: assert property (
    @(posedge clk) disable iff (!reset) $rose(rst_out) |-> ($past(reset,2) &&  $past(Vin < Vth,1) && !$past(Vin < Vth,2))
  );

  // A falling edge on rst_out matches a 1->0 transition of (Vin < Vth) in the prior cycle.
  check_out_fall_matches_comp_fall: assert property (
    @(posedge clk) disable iff (!reset) $fell(rst_out) |-> ($past(reset,2) && !$past(Vin < Vth,1) &&  $past(Vin < Vth,2))
  );

  // If (Vin < Vth) is unchanged over the last two cycles, rst_out is stable now.
  check_out_stable_when_comp_unchanged: assert property (
    @(posedge clk) disable iff (!reset) ($past(reset,2) && ($past(Vin < Vth,1) == $past(Vin < Vth,2))) |-> $stable(rst_out)
  );

  // On reset deassertion cycle, rst_out remains 0 (update occurs after sampling).
  check_out_zero_on_reset_rise_cycle: assert property (
    @(posedge clk) disable iff (!reset) $rose(reset) |-> (rst_out == 1'b0)
  );

endmodule