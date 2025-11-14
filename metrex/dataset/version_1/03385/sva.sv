// SVA checker for Calculator
module Calculator_sva (
  input logic        clk,
  input logic        rst,
  input logic [7:0]  A,
  input logic [7:0]  B,
  input logic [1:0]  op,
  input logic [7:0]  result
);

  default clocking cb @(posedge clk); endclocking

  // Reset behavior
  property p_rst_to_zero;
    rst |=> result == 8'h00;
  endproperty
  assert property (p_rst_to_zero);

  property p_rst_hold_zero;
    rst && $past(rst) |-> result == 8'h00;
  endproperty
  assert property (p_rst_hold_zero);

  // Functional correctness (1-cycle latency)
  // Add
  property p_add;
    disable iff (rst)
      (op == 2'b00) |=> result == ({1'b0,$past(A)} + {1'b0,$past(B)})[7:0];
  endproperty
  assert property (p_add);

  // Sub
  property p_sub;
    disable iff (rst)
      (op == 2'b01) |=> result == ({1'b0,$past(A)} - {1'b0,$past(B)})[7:0];
  endproperty
  assert property (p_sub);

  // Mul (low 8 bits)
  property p_mul;
    disable iff (rst)
      (op == 2'b10) |=> result == (($past(A) * $past(B)) & 16'h00FF);
  endproperty
  assert property (p_mul);

  // Div: forbid divide-by-zero, and check quotient when legal
  property p_div_nozero;
    disable iff (rst)
      (op == 2'b11) |-> (B != 8'h00);
  endproperty
  assert property (p_div_nozero);

  property p_div_q;
    disable iff (rst)
      (op == 2'b11 && B != 8'h00) |=> result == ($past(A) / $past(B));
  endproperty
  assert property (p_div_q);

  // No X on result when operation is legal
  property p_no_x_on_result;
    disable iff (rst)
      !(op == 2'b11 && B == 8'h00) |=> !$isunknown(result);
  endproperty
  assert property (p_no_x_on_result);

  // Coverage
  cover property (disable iff (rst) op == 2'b00 ##1 result == ({1'b0,$past(A)} + {1'b0,$past(B)})[7:0]);
  cover property (disable iff (rst) op == 2'b01 ##1 result == ({1'b0,$past(A)} - {1'b0,$past(B)})[7:0]);
  cover property (disable iff (rst) op == 2'b10 ##1 result == (($past(A) * $past(B)) & 16'h00FF));
  cover property (disable iff (rst) op == 2'b11 && B != 8'h00 ##1 result == ($past(A) / $past(B)));

  // Edge-case coverage
  cover property (disable iff (rst) (op == 2'b00) && ({1'b0,A} + {1'b0,B})[8]);               // add carry out
  cover property (disable iff (rst) (op == 2'b01) && (A < B));                                 // sub borrow
  cover property (disable iff (rst) (op == 2'b10) && ((A * B)[15:8] != 8'h00));                // mul overflow
  cover property (disable iff (rst) (op == 2'b11 && B != 8'h00) && ($past(A) % $past(B) == 0));// div exact
  cover property (disable iff (rst) (op == 2'b11 && B != 8'h00) && ($past(A) % $past(B) != 0));// div remainder
  cover property (rst ##1 !rst);                                                               // reset release

endmodule

// Bind into DUT
bind Calculator Calculator_sva u_calculator_sva (
  .clk(clk),
  .rst(rst),
  .A(A),
  .B(B),
  .op(op),
  .result(result)
);