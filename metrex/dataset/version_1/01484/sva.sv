// SVA for the provided design. Focused, concise, and binding-based.
// Put this in a separate .sv file and compile with the DUT.

package dut_sva_pkg;
  // Utility
  function automatic logic [31:0] byte_rev32(input logic [31:0] v);
    return {v[7:0], v[15:8], v[23:16], v[31:24]};
  endfunction
endpackage


// ---------------- adder_subtractor ----------------
module adder_subtractor_sva (
  input logic [31:0] a,
  input logic [31:0] b,
  input logic        sub,
  input logic [31:0] sum,
  input logic [31:0] sum_reverse
);
  import dut_sva_pkg::*;

  // Functional correctness (combinational settle via ##0)
  property p_addsub_correct;
    @(a or b or sub) ##0 (sum == (sub ? a - b : a + b));
  endproperty
  assert property (p_addsub_correct);

  property p_rev_correct;
    @(a or b or sub or sum) ##0 (sum_reverse == byte_rev32(sum));
  endproperty
  assert property (p_rev_correct);

  // No X/Z on outputs when inputs known
  property p_no_x;
    @(a or b or sub)
      (!$isunknown({a,b,sub})) |-> ##0 (!$isunknown({sum,sum_reverse}));
  endproperty
  assert property (p_no_x);

  // Minimal functional coverage
  cover property (@(a or b or sub) (sub==1'b0) ##0 1);
  cover property (@(a or b or sub) (sub==1'b1) ##0 1);
  cover property (@(a or b or sub) (sub==1'b0) ##0 (sum < a)); // unsigned add carry
  cover property (@(a or b or sub) (sub==1'b1) ##0 (sum > a)); // unsigned sub borrow
  cover property (@(a or b or sub) (sub==1'b1 && a==b) ##0 (sum==32'h0));
endmodule
bind adder_subtractor adder_subtractor_sva sva_addsub (.*);


// ---------------- byte_reversal ----------------
module byte_reversal_sva (
  input logic [31:0] input_data,
  input logic [31:0] output_data
);
  import dut_sva_pkg::*;

  property p_rev;
    @(input_data) ##0 (output_data == byte_rev32(input_data));
  endproperty
  assert property (p_rev);

  // No X/Z on output when input known
  assert property (@(input_data) !$isunknown(input_data) |-> ##0 !$isunknown(output_data));

  // Coverage: exercise reversal with differing bytes
  cover property (@(input_data) (input_data==32'h00000000));
  cover property (@(input_data) (input_data==32'hFFFFFFFF));
  cover property (@(input_data) (input_data==32'hA1B2C3D4));
endmodule
bind byte_reversal byte_reversal_sva sva_brev (.*);


// ---------------- functional_module ----------------
module functional_module_sva (
  input logic [31:0] input1,
  input logic [31:0] input2,
  input logic [31:0] final_output
);
  property p_add;
    @(input1 or input2) ##0 (final_output == input1 + input2);
  endproperty
  assert property (p_add);

  assert property (@(input1 or input2) !$isunknown({input1,input2}) |-> ##0 !$isunknown(final_output));

  // Coverage: unsigned overflow on add
  cover property (@(input1 or input2) ##0 (final_output < input1));
endmodule
bind functional_module functional_module_sva sva_func (.*);


// ---------------- top_module (end-to-end) ----------------
module top_module_sva (
  input logic [31:0] a,
  input logic [31:0] b,
  input logic        sub,
  input logic [31:0] sum,
  input logic [31:0] sum_reverse,
  input logic [31:0] final_output
);
  import dut_sva_pkg::*;

  // End-to-end functional checks
  assert property (@(a or b or sub) ##0 (sum == (sub ? a - b : a + b)));
  assert property (@(a or b or sub or sum) ##0 (sum_reverse == byte_rev32(sum)));
  assert property (@(a or b or sub) ##0 (final_output == sum + sum_reverse));

  // Sanity: outputs known when inputs known
  assert property (@(a or b or sub) !$isunknown({a,b,sub}) |-> ##0 !$isunknown({sum,sum_reverse,final_output}));

  // Coverage: both ops, reversal visible, and extreme operands
  cover property (@(a or b or sub) (sub==0));
  cover property (@(a or b or sub) (sub==1));
  cover property (@(a or b or sub) ##0 (sum_reverse != sum));
  cover property (@(a or b or sub) (a==32'h0 && b==32'h0));
  cover property (@(a or b or sub) (a==32'hFFFF_FFFF && b==32'hFFFF_FFFF));
endmodule
bind top_module top_module_sva sva_top (.*);