// SVA for wire_recorder
module wire_recorder_sva (
  input logic                  clk,
  input logic                  reset,
  input logic [156:0]          input_vector,
  input logic [129:0]          output_vector,
  input logic [156:0]          input_vector_reg,
  input logic [129:0]          output_vector_reg,
  input logic                  clk_start
);

  default clocking cb @(posedge clk); endclocking

  // Synchronous reset clears all regs in the same cycle
  assert property (reset |-> ##0 (input_vector_reg == '0 && output_vector_reg == '0 && clk_start == 1'b0));

  // Registering of inputs/outputs on non-reset cycles (same-cycle NBA effect)
  assert property (!reset |-> ##0 (input_vector_reg == input_vector));
  assert property (!reset |-> ##0 (output_vector_reg == output_vector));

  // clk_start monotonic high until reset
  assert property (disable iff (reset) !$fell(clk_start));

  // Rising clk_start must be caused by prior output_vector_reg[0]==1 (and hence prior output_vector[0]==1)
  assert property (disable iff (reset) $rose(clk_start) |-> $past(output_vector_reg[0]));
  assert property (disable iff (reset) $rose(clk_start) |-> $past(output_vector[0]));

  // If prior output_vector_reg[0]==1, clk_start must be 1 now; else it must hold its value
  assert property (disable iff (reset) $past(output_vector_reg[0]) |-> clk_start);
  assert property (disable iff (reset) !$past(output_vector_reg[0]) |-> (clk_start == $past(clk_start)));

  // No X/Z on registered outputs when out of reset
  assert property (disable iff (reset) !$isunknown({input_vector_reg, output_vector_reg, clk_start}));

  // Coverage
  cover property (reset ##1 !reset);
  cover property (disable iff (reset) (!clk_start ##1 $rose(clk_start)));
  cover property (disable iff (reset) (output_vector[0] ##1 clk_start));
  cover property (disable iff (reset) ($changed(input_vector) ##1 (input_vector_reg == $past(input_vector))));
  cover property (disable iff (reset) $rose(output_vector[0]));

endmodule

// Bind into DUT
bind wire_recorder wire_recorder_sva sva_wire_recorder (.*);