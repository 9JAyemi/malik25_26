// SVA for shift_register
// Bind into the DUT to check behavior and collect coverage.
module shift_register_sva #(parameter DW=16)
(
  input clk,
  input rst,
  input ena,
  input [DW-1:0] data_in,
  input [DW-1:0] data_out
);
  default clocking cb @(posedge clk); endclocking

  // Output must mirror stage 2
  a_out_matches_stage2: assert property (data_out == pipeline_reg[2]);

  // Synchronous reset clears both pipeline stages
  a_reset_clears: assert property (@(posedge clk) rst |=> (pipeline_reg[1]=={DW{1'b0}} && pipeline_reg[2]=={DW{1'b0}}));

  // Load behavior when ena=1
  a_ena_loads: assert property (disable iff (rst)
                                ena |=> (pipeline_reg[1]==$past(data_in) &&
                                         pipeline_reg[2]==$past(pipeline_reg[1])));

  // Shift/feedback behavior when ena=0
  a_shift_feedback: assert property (disable iff (rst)
                                     !ena |=> (pipeline_reg[1]==$past(pipeline_reg[2]) &&
                                               pipeline_reg[2]==($past(pipeline_reg[1])<<1)));

  // Output latency under back-to-back loads (ena held high)
  a_latency_under_load: assert property (disable iff (rst)
                                         $past(ena) && ena |-> data_out == $past(data_in));

  // No X/Z on key signals after reset is deasserted
  a_no_unknowns: assert property (disable iff (rst)
                                  !$isunknown({ena, data_out, pipeline_reg[1], pipeline_reg[2]}));

  // Coverage
  c_reset_pulse:   cover property (@(posedge clk) rst ##1 !rst);
  c_ena_path:      cover property (disable iff (rst) ena);
  c_shift_path:    cover property (disable iff (rst) !ena);
  c_toggle_paths:  cover property (disable iff (rst) ena ##1 !ena ##1 ena);
  c_shift_overflow:cover property (disable iff (rst) $past(!ena) && $past(pipeline_reg[1][DW-1]));

endmodule

bind shift_register shift_register_sva #(.DW(16)) u_shift_register_sva (.*);