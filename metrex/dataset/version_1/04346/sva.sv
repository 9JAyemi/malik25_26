// SVA for or3 and three_input_module (concise, quality-focused)
`ifndef THREE_INPUT_MODULE_SVA
`define THREE_INPUT_MODULE_SVA

// Assertions for leaf OR gate
module or3_sva();
  // Bound inside or3; sample on any relevant change
  default clocking cb @(posedge A or negedge A or
                         posedge B or negedge B or
                         posedge C or negedge C or
                         posedge VPWR or negedge VPWR or
                         posedge VGND or negedge VGND); endclocking
  wire power_good = (VPWR === 1'b1) && (VGND === 1'b0);
  wire in_known   = !$isunknown({A,B,C});

  // Functional correctness and X-propagation control when powered and inputs known
  a_or3_func:  assert property (disable iff (!power_good) in_known |-> (X === (A | B | C)));
  a_or3_xfree: assert property (disable iff (!power_good) in_known |-> !$isunknown(X));

  // Basic truth-table coverage (power-good)
  c_or3_000: cover property (power_good && {A,B,C} == 3'b000);
  c_or3_001: cover property (power_good && {A,B,C} == 3'b001);
  c_or3_010: cover property (power_good && {A,B,C} == 3'b010);
  c_or3_011: cover property (power_good && {A,B,C} == 3'b011);
  c_or3_100: cover property (power_good && {A,B,C} == 3'b100);
  c_or3_101: cover property (power_good && {A,B,C} == 3'b101);
  c_or3_110: cover property (power_good && {A,B,C} == 3'b110);
  c_or3_111: cover property (power_good && {A,B,C} == 3'b111);
endmodule

// Assertions for top module
module three_input_module_sva();
  // Bound inside three_input_module
  default clocking cb @(posedge input_a or negedge input_a or
                         posedge input_b or negedge input_b or
                         posedge input_c or negedge input_c or
                         posedge vpwr    or negedge vpwr    or
                         posedge vgnd    or negedge vgnd); endclocking
  wire power_good = (vpwr === 1'b1) && (vgnd === 1'b0);
  wire in_known   = !$isunknown({input_a,input_b,input_c});

  // Internal functional checks (including redundancy equivalences)
  a_or1_eq:  assert property (disable iff (!power_good) in_known |-> (or1_output === (input_a | input_b | input_c)));
  a_or2_eq:  assert property (disable iff (!power_good) !$isunknown(or1_output) |-> (or2_output === (input_a | input_b | or1_output)));
  a_or2_red: assert property (disable iff (!power_good) !$isunknown(or1_output) |-> (or2_output === or1_output));
  a_or3_eq:  assert property (disable iff (!power_good) (!$isunknown({or1_output,or2_output}) && in_known) |-> (or3_output === (or2_output | input_c | or1_output)));
  a_or3_red: assert property (disable iff (!power_good) !$isunknown(or1_output) |-> (or3_output === or1_output));

  // Output checks
  a_out_inv3: assert property (disable iff (!power_good) !$isunknown(or3_output) |-> (output_x === ~or3_output));
  a_out_nor:  assert property (disable iff (!power_good) in_known |-> (output_x === ~(input_a | input_b | input_c)));
  a_out_known:assert property (disable iff (!power_good) in_known |-> !$isunknown(output_x));

  // Input-state coverage under power-good
  c_top_000: cover property (power_good && {input_a,input_b,input_c} == 3'b000);
  c_top_001: cover property (power_good && {input_a,input_b,input_c} == 3'b001);
  c_top_010: cover property (power_good && {input_a,input_b,input_c} == 3'b010);
  c_top_011: cover property (power_good && {input_a,input_b,input_c} == 3'b011);
  c_top_100: cover property (power_good && {input_a,input_b,input_c} == 3'b100);
  c_top_101: cover property (power_good && {input_a,input_b,input_c} == 3'b101);
  c_top_110: cover property (power_good && {input_a,input_b,input_c} == 3'b110);
  c_top_111: cover property (power_good && {input_a,input_b,input_c} == 3'b111);

  // Output toggle coverage (NOR behavior) under power-good
  c_out_10: cover property (power_good && $past(power_good) && $past(output_x) && !output_x);
  c_out_01: cover property (power_good && $past(power_good) && !$past(output_x) && output_x);
endmodule

// Bind SVA to DUTs
bind or3                or3_sva                 or3_sva_i();
bind three_input_module three_input_module_sva  three_input_module_sva_i();

`endif