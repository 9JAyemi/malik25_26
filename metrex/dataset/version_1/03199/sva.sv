// SVA for add_sub. Bind this to the DUT.
// Checks correct result and overflow semantics, with concise coverage.

module add_sub_sva (
  input logic [7:0] a,
  input logic [7:0] b,
  input logic       add_sub_ctrl, // 0:add, 1:sub
  input logic [7:0] result,
  input logic       overflow
);

  // 9-bit reference arithmetic
  let sum9       = {1'b0, a} + {1'b0, b};
  let diff9      = {1'b0, a} + {1'b0, ~b} + 9'd1;     // a - b
  let exp_add_res = sum9[7:0];
  let exp_sub_res = diff9[7:0];

  // Overflow definitions:
  // - Addition: unsigned carry-out
  // - Subtraction: signed overflow in 2's complement
  let exp_add_ov = sum9[8];
  let exp_sub_ov = ((a[7] != b[7]) && (exp_sub_res[7] != a[7]));

  // No-X on outputs when inputs are known
  property p_no_x;
    @(a or b or add_sub_ctrl)
      (!$isunknown({a,b,add_sub_ctrl})) |-> ##0 (!$isunknown({result,overflow}));
  endproperty
  assert property (p_no_x);

  // Addition result and overflow
  property p_add_correct;
    @(a or b or add_sub_ctrl)
      (!add_sub_ctrl && !$isunknown({a,b,add_sub_ctrl}))
      |-> ##0 (result == exp_add_res && overflow == exp_add_ov);
  endproperty
  assert property (p_add_correct);

  // Subtraction result and overflow (2's complement overflow)
  property p_sub_correct;
    @(a or b or add_sub_ctrl)
      (add_sub_ctrl && !$isunknown({a,b,add_sub_ctrl}))
      |-> ##0 (result == exp_sub_res && overflow == exp_sub_ov);
  endproperty
  assert property (p_sub_correct);

  // Functional coverage (concise, key scenarios)
  // Addition: no carry and carry-out
  cover property (@(a or b or add_sub_ctrl) !add_sub_ctrl && !exp_add_ov);
  cover property (@(a or b or add_sub_ctrl) !add_sub_ctrl &&  exp_add_ov);
  // Subtraction: no overflow and overflow
  cover property (@(a or b or add_sub_ctrl)  add_sub_ctrl && !exp_sub_ov);
  cover property (@(a or b or add_sub_ctrl)  add_sub_ctrl &&  exp_sub_ov);
  // Wrap/identity cases
  cover property (@(a or b or add_sub_ctrl) !add_sub_ctrl && (exp_add_res == 8'h00)); // add wrap
  cover property (@(a or b or add_sub_ctrl)  add_sub_ctrl && (a == b) && (result == 8'h00)); // a-b=0
  // Borrow vs no-borrow in subtraction (unsigned perspective)
  cover property (@(a or b or add_sub_ctrl)  add_sub_ctrl && ({1'b0,a} < {1'b0,b}));
  cover property (@(a or b or add_sub_ctrl)  add_sub_ctrl && ({1'b0,a} >= {1'b0,b}));

endmodule

// Bind into DUT
bind add_sub add_sub_sva add_sub_sva_i (
  .a(a),
  .b(b),
  .add_sub_ctrl(add_sub_ctrl),
  .result(result),
  .overflow(overflow)
);