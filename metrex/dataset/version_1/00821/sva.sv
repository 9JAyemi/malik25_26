// SVA for simple_calculator
// Bind this module to the DUT: bind simple_calculator simple_calculator_sva sva(.clk(clk), .rst(rst), .op(op), .num1(num1), .num2(num2), .result(result), .overflow(overflow));

module simple_calculator_sva(
  input logic                  clk,
  input logic                  rst,
  input logic [1:0]            op,
  input logic signed [7:0]     num1,
  input logic signed [7:0]     num2,
  input logic signed [7:0]     result,
  input logic                  overflow
);

  // Common helpers (sampled at the antecedent cycle)
  let add9  = $signed(num1) + $signed(num2);                     // 9-bit signed
  let sub9  = $signed(num1) - $signed(num2);                     // 9-bit signed
  let mul16 = $signed(num1) * $signed(num2);                     // 16-bit signed

  let add_res  = add9[7:0];
  let add_ovf  = (add9[8] != add9[7]);                           // top two bits differ => overflow
  let sub_res  = sub9[7:0];
  let sub_ovf  = (sub9[8] != sub9[7]);
  let mul_res  = mul16[7:0];
  let mul_ovf  = (mul16[15:8] != {8{mul16[7]}});                 // not a proper sign-extension

  // Reset behavior
  property p_reset_sync;
    @(posedge clk) rst |=> (result == 0 && overflow == 0);
  endproperty
  assert property(p_reset_sync);

  // Known outputs when not in reset
  assert property(@(posedge clk) disable iff (rst) !$isunknown({result, overflow}));

  // Addition
  property p_add;
    @(posedge clk) disable iff (rst)
      (op == 2'b00) |=> (result == add_res && overflow == add_ovf);
  endproperty
  assert property(p_add);

  // Subtraction
  property p_sub;
    @(posedge clk) disable iff (rst)
      (op == 2'b01) |=> (result == sub_res && overflow == sub_ovf);
  endproperty
  assert property(p_sub);

  // Multiplication (truncation to 8b, overflow if sign-extension not preserved)
  property p_mul;
    @(posedge clk) disable iff (rst)
      (op == 2'b10) |=> (result == mul_res && overflow == mul_ovf);
  endproperty
  assert property(p_mul);

  // Division by zero
  property p_div_by_zero;
    @(posedge clk) disable iff (rst)
      (op == 2'b11 && num2 == 0) |=> (result == 0 && overflow == 1);
  endproperty
  assert property(p_div_by_zero);

  // Division normal (signed trunc toward zero, no overflow)
  property p_div_normal;
    @(posedge clk) disable iff (rst)
      (op == 2'b11 && num2 != 0) |=> (result == ($signed(num1) / $signed(num2)) && overflow == 0);
  endproperty
  assert property(p_div_normal);

  // Minimal, meaningful functional coverage
  // Ops exercised
  cover property(@(posedge clk) disable iff (rst) op == 2'b00);
  cover property(@(posedge clk) disable iff (rst) op == 2'b01);
  cover property(@(posedge clk) disable iff (rst) op == 2'b10);
  cover property(@(posedge clk) disable iff (rst) op == 2'b11);

  // Overflow/no-overflow per arithmetic op
  cover property(@(posedge clk) disable iff (rst) (op == 2'b00) ##1 overflow);
  cover property(@(posedge clk) disable iff (rst) (op == 2'b00) ##1 !overflow);
  cover property(@(posedge clk) disable iff (rst) (op == 2'b01) ##1 overflow);
  cover property(@(posedge clk) disable iff (rst) (op == 2'b01) ##1 !overflow);
  cover property(@(posedge clk) disable iff (rst) (op == 2'b10) ##1 overflow);
  cover property(@(posedge clk) disable iff (rst) (op == 2'b10) ##1 !overflow);

  // Division paths
  cover property(@(posedge clk) disable iff (rst) (op == 2'b11 && num2 == 0));
  cover property(@(posedge clk) disable iff (rst) (op == 2'b11 && num2 != 0));

endmodule