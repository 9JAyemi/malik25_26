// SVA checker for dffsr
module dffsr_sva (
  input logic clk,
  input logic d,
  input logic set,
  input logic reset,
  input logic preset,
  input logic q,
  input logic q_bar
);

  // Sample after NBA to see updated flop outputs
  default clocking cb @(posedge clk);
    input #1step d, set, reset, preset, q, q_bar;
  endclocking

  // Priority and functional correctness
  assert property (@cb reset                        |-> (q==1'b0 && q_bar==1'b1));
  assert property (@cb (!reset && set)              |-> (q==1'b1 && q_bar==1'b0));
  assert property (@cb (!reset && !set && preset)   |-> (q==1'b1 && q_bar==1'b0));
  assert property (@cb (!reset && !set && !preset)  |-> (q==d    && q_bar==~d));

  // q_bar must be complement of q whenever known
  assert property (@cb (!$isunknown({q,q_bar})) |-> (q_bar == ~q));

  // Coverage: hit all branches and key overlaps
  cover property (@cb reset);
  cover property (@cb !reset && set);
  cover property (@cb !reset && !set && preset);
  cover property (@cb !reset && !set && !preset);
  cover property (@cb reset && set);
  cover property (@cb !reset && set && preset);
  cover property (@cb reset && set && preset);
  // Data-path toggle under normal operation
  cover property (@cb (!reset && !set && !preset) ##1 (!reset && !set && !preset && (d != $past(d))));

endmodule

// Bind into DUT
bind dffsr dffsr_sva sva_inst(.clk(clk), .d(d), .set(set), .reset(reset), .preset(preset), .q(q), .q_bar(q_bar));