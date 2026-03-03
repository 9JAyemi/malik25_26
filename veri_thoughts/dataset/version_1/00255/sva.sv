// SVA checker for comparator (binds to DUT; no DUT changes needed)
module comparator_sva (
  input logic [1:0] in_0,
  input logic [1:0] in_1,
  input logic [1:0] out
);

  function automatic logic [1:0] exp (input logic [1:0] a, input logic [1:0] b);
    exp = (a > b) ? 2'b01 : ((a == b) ? 2'b10 : 2'b00);
  endfunction

  // Functional correctness when inputs are known
  property p_func_ok;
    @(in_0 or in_1) !$isunknown({in_0,in_1}) |-> ##0 (out == exp(in_0,in_1));
  endproperty
  assert property(p_func_ok);

  // Output is 2-state when inputs are 2-state
  property p_no_x_out_when_inputs_known;
    @(in_0 or in_1) !$isunknown({in_0,in_1}) |-> ##0 !$isunknown(out);
  endproperty
  assert property(p_no_x_out_when_inputs_known);

  // Output always a legal code (00,01,10)
  property p_legal_code;
    @(out) 1 |-> ##0 (out inside {2'b00,2'b01,2'b10});
  endproperty
  assert property(p_legal_code);

  // No output toggle without an input toggle
  property p_no_spurious_toggle;
    @(out) 1 |-> ##0 ($changed(in_0) || $changed(in_1));
  endproperty
  assert property(p_no_spurious_toggle);

  // Coverage: hit all three outcomes (with known inputs)
  cover property (@(in_0 or in_1) !$isunknown({in_0,in_1}) ##0 (out == 2'b01)); // in_0 > in_1
  cover property (@(in_0 or in_1) !$isunknown({in_0,in_1}) ##0 (out == 2'b10)); // in_0 == in_1
  cover property (@(in_0 or in_1) !$isunknown({in_0,in_1}) ##0 (out == 2'b00)); // in_0 < in_1

endmodule

bind comparator comparator_sva i_comparator_sva (.in_0(in_0), .in_1(in_1), .out(out));