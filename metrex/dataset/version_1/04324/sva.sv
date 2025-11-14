// SVA for the provided design. Bind these checkers to the DUTs.

module adder_32bit_sva;
  // Expect pure combinational: sample on any change
  wire inputs_known = !$isunknown({a,b});
  wire [32:0] exp_sum = {1'b0,a} + {1'b0,b};

  // Functional correctness
  assert property (@(*) inputs_known |-> (sum == exp_sum[31:0]));

  // Carry-out consistency (uses internal 'carry' net as implemented)
  assert property (@(*) inputs_known |-> (carry[0] == exp_sum[32]));

  // Basic bit 0 sanity
  assert property (@(*) inputs_known |-> (sum[0] == (a[0]^b[0])));

  // No X on outputs when inputs are known
  assert property (@(*) inputs_known |-> !$isunknown(sum));

  // Coverage: carry-out, zero result, canonical wrap case, signed overflow
  cover property (@(*) inputs_known && (exp_sum[32] == 1'b1));
  cover property (@(*) inputs_known && (sum == 32'h0000_0000));
  cover property (@(*) inputs_known && (a == 32'hFFFF_FFFF && b == 32'h0000_0001));
  cover property (@(*) inputs_known && (a[31] == b[31]) && (sum[31] != a[31]));
endmodule
bind adder_32bit adder_32bit_sva adder_32bit_sva_i();


module bitwise_logic_3bit_sva;
  wire inputs_known = !$isunknown({a,b});
  wire [2:0] exp_or  = a | b;
  wire       exp_lor = (|a) || (|b);
  wire [5:0] exp_not = {~b, ~a};

  // Functional correctness
  assert property (@(*) inputs_known |-> (out_or == exp_or));
  assert property (@(*) inputs_known |-> (out_logical_or == exp_lor));
  assert property (@(*) inputs_known |-> (out_not == exp_not));

  // No X on outputs when inputs are known
  assert property (@(*) inputs_known |-> !$isunknown({out_or, out_logical_or, out_not}));

  // Coverage: zeros, all ones, mixed pattern
  cover property (@(*) a == 3'b000 && b == 3'b000);
  cover property (@(*) a == 3'b111 && b == 3'b111);
  cover property (@(*) a == 3'b101 && b == 3'b010);
endmodule
bind bitwise_logic_3bit bitwise_logic_3bit_sva bitwise_logic_3bit_sva_i();


module top_module_sva;
  wire inputs_known = !$isunknown({a,b,in_bitwise_a,in_bitwise_b});

  // Expected golden computation from top inputs
  wire [32:0] exp_add   = {1'b0,a} + {1'b0,b};
  wire [5:0]  exp_not   = {~in_bitwise_b, ~in_bitwise_a};
  wire [2:0]  exp_or    = in_bitwise_a | in_bitwise_b;
  wire        exp_lor   = (|in_bitwise_a) || (|in_bitwise_b);
  wire [11:0] exp_not12 = {exp_not[5:3], exp_not[2:0], exp_not[5:3], exp_not[2:0]};
  wire [5:0]  exp_or6   = {exp_or[2], exp_or[1], exp_or[0], 3'b000};

  // Outputs must match golden behavior
  assert property (@(*) inputs_known |-> (out_or_bitwise == exp_or));
  assert property (@(*) inputs_known |-> (out_or_logical == exp_lor));
  assert property (@(*) inputs_known |-> (out_not == exp_not));
  assert property (@(*) inputs_known |-> (final_output == (exp_add[31:0] + exp_not12 + exp_or6)));

  // No X on outputs when inputs are known
  assert property (@(*) inputs_known |-> !$isunknown({final_output, out_or_bitwise, out_or_logical, out_not}));

  // Coverage: OR/NOT extremes and adder carry-out influencing final_output
  cover property (@(*) inputs_known && (in_bitwise_a == 3'b000 && in_bitwise_b == 3'b000));
  cover property (@(*) inputs_known && (in_bitwise_a == 3'b111 && in_bitwise_b == 3'b111));
  cover property (@(*) inputs_known && (exp_add[32] == 1'b1));
endmodule
bind top_module top_module_sva top_module_sva_i();