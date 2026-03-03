// SVA checker for absolute_value_calculator
module absolute_value_calculator_sva #(parameter int W = 8)
(
  input  logic signed [W-1:0] input_num,
  input  logic        [W-1:0] abs_value
);

  // Sample on any simulation time advance
  default clocking cb @($global_clock); endclocking

  localparam signed [W-1:0] MIN_NEG = {1'b1, {W-1{1'b0}}}; // -2^(W-1)
  localparam        [W-1:0] MAX_MAG = {1'b0, {W-1{1'b1}}}; //  2^(W-1)-1

  // X-prop: known input implies known output
  assert property (!$isunknown(input_num)) |-> (!$isunknown(abs_value));

  // Functional spec (absolute value)
  assert property (abs_value == (input_num[W-1] ? (~input_num + 1'b1) : input_num));

  // Special-case: minimum negative maps to 2^(W-1)
  assert property (input_num == MIN_NEG |-> abs_value == {1'b1, {W-1{1'b0}}});

  // Otherwise magnitude fits in [0 .. 2^(W-1)-1]
  assert property (input_num != MIN_NEG |-> abs_value <= MAX_MAG);

  // Branch-specific checks
  assert property (!input_num[W-1] |-> abs_value == input_num);
  assert property ( input_num[W-1] |-> abs_value == (~input_num + 1'b1));

  // Coverage: both branches and key corner cases
  cover  property (!input_num[W-1]);                       // non-negative path
  cover  property ( input_num[W-1]);                       // negative path
  cover  property (input_num == {W{1'b0}});                // zero
  cover  property (input_num == MIN_NEG);                  // -2^(W-1)
  cover  property (input_num == MAX_MAG);                  // +2^(W-1)-1
  cover  property (input_num == {1'b1, {W-1{1'b1}}});      // -1
  cover  property ( input_num[W-1] ##1 !input_num[W-1]);   // sign flip -
  cover  property (!input_num[W-1] ##1  input_num[W-1]);   // sign flip +
endmodule

// Bind into the DUT
bind absolute_value_calculator
  absolute_value_calculator_sva #(.W(8)) abs_val_calc_sva_i
  (.input_num(input_num), .abs_value(abs_value));