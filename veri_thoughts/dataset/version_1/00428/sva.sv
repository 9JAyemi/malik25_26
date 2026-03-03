// Bindable SVA for calculator
module calc_sva(
  input logic        clk,
  input logic        rst,
  input logic [1:0]  op,
  input logic [3:0]  num1,
  input logic [3:0]  num2,
  input logic [3:0]  result,
  input logic        overflow
);

  default clocking @(posedge clk); endclocking
  default disable iff (rst);

  // Golden, width-safe intermediates
  let sum5  = {1'b0, num1} + {1'b0, num2};        // 5-bit add
  let diff5 = {1'b0, num1} - {1'b0, num2};        // 5-bit sub (MSB=borrow)
  let prod8 = num1 * num2;                        // 8-bit mul

  // Arithmetic correctness (lower 4 bits)
  assert property (op==2'b00 |-> result == sum5[3:0])  else $error("ADD result mismatch");
  assert property (op==2'b01 |-> result == diff5[3:0]) else $error("SUB result mismatch");
  assert property (op==2'b10 |-> result == prod8[3:0]) else $error("MUL result mismatch");
  assert property ((op==2'b11) && (num2!=0) |-> result == (num1 / num2)) else $error("DIV result mismatch");

  // Overflow/exception semantics
  assert property (op==2'b00 |-> overflow == sum5[4])                       else $error("ADD overflow mismatch");
  assert property (op==2'b01 |-> overflow == (num1 < num2))                 else $error("SUB underflow mismatch");
  assert property (op==2'b10 |-> overflow == (|prod8[7:4]))                 else $error("MUL overflow mismatch");
  assert property ((op==2'b11) && (num2!=0) |-> overflow == 1'b0)           else $error("DIV overflow should be 0 when denom!=0");
  assert property ((op==2'b11) && (num2==0) |-> overflow == 1'b1)           else $error("DIV by zero must flag overflow");

  // X-propagation/clean outputs (except div-by-zero case)
  assert property (!$isunknown({op,num1,num2}) && !(op==2'b11 && num2==0)
                   |-> !$isunknown({result,overflow}))
    else $error("Unexpected X/Z on outputs with valid inputs");

  // Basic op legality (op is 2 bits; ensure no X)
  assert property (!$isunknown(op)) else $error("op contains X/Z");

  // Functional coverage
  cover property (op==2'b00 && (sum5[4]==0)); // add no carry
  cover property (op==2'b00 && (sum5[4]==1)); // add carry
  cover property (op==2'b01 && !(num1<num2)); // sub no borrow
  cover property (op==2'b01 &&  (num1<num2)); // sub borrow
  cover property (op==2'b10 && (|prod8[7:4])==0); // mul no overflow
  cover property (op==2'b10 && (|prod8[7:4])==1); // mul overflow
  cover property (op==2'b11 && (num2!=0)); // normal division
  cover property (op==2'b11 && (num2==0)); // divide by zero

endmodule

// Bind into DUT
bind calculator calc_sva u_calc_sva(.clk(clk), .rst(rst), .op(op), .num1(num1), .num2(num2), .result(result), .overflow(overflow));