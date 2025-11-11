// SVA for top_module (bindable, concise, high-quality checks)

module top_module_sva (
  input logic        clk,
  input logic        reset,
  input logic [7:0]  d1,
  input logic [7:0]  d2,
  input logic [7:0]  reg1,
  input logic [7:0]  reg2,
  input logic [7:0]  add_result,
  input logic [7:0]  mul_result,
  input logic [7:0]  q,
  input logic [7:0]  mult_b
);
  default clocking cb @(posedge clk); endclocking

  // Structural/constant checks
  assert property (mult_b == 8'd5);

  // Reset behavior (sync reset visible next cycle)
  assert property (reset |=> (reg1 == 8'h00 && reg2 == 8'h00));

  // Register load (only when current and previous cycles are not in reset)
  assert property ((!reset && !$past(reset)) |-> (reg1 == $past(d1) && reg2 == $past(d2)));

  // Combinational functionality (mod-256 arithmetic)
  assert property (add_result == ((reg1 + reg2) & 8'hFF));
  assert property (mul_result == ((add_result * 8'd5) & 8'hFF));
  assert property (q == mul_result);

  // End-to-end: q reflects previous-cycle inputs
  assert property ((!reset && !$past(reset)) |-> (q == ((($past(d1) + $past(d2)) * 8'd5) & 8'hFF)));

  // No X/Z on key nets
  assert property (!$isunknown({reg1,reg2,add_result,mul_result,q}));

  // Coverage (reset, add overflow, mul overflow, zero output)
  cover property (reset ##1 !reset);
  cover property ((!reset && !$past(reset)) && (({1'b0,reg1} + {1'b0,reg2})[8] == 1'b1)); // add overflow
  cover property (!reset && (add_result >= 8'd52)); // mul overflow (since 52*5 > 255)
  cover property (!reset && q == 8'h00);
endmodule

bind top_module top_module_sva sva_top (
  .clk(clk),
  .reset(reset),
  .d1(d1),
  .d2(d2),
  .reg1(reg1),
  .reg2(reg2),
  .add_result(add_result),
  .mul_result(mul_result),
  .q(q),
  .mult_b(multiplier.b)
);