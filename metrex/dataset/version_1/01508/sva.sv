// SVA checker for calculator. Bind this and provide a sampling clock.
module calculator_sva (
  input logic              clk,
  input logic [7:0]        a, b,
  input logic [1:0]        op,
  input logic [7:0]        result
);
  default clocking cb @(posedge clk); endclocking

  function automatic bit known_inputs();
    return !$isunknown({a,b,op});
  endfunction

  // Correctness per operation (mod 256 for +, -, *)
  a_add: assert property ( known_inputs() && op==2'b00 |-> result == logic [7:0]'(a + b) );
  a_sub: assert property ( known_inputs() && op==2'b01 |-> result == logic [7:0]'(a - b) );
  a_mul: assert property ( known_inputs() && op==2'b10 |-> result == logic [7:0]'(a * b) );
  a_div: assert property ( known_inputs() && op==2'b11 && (b!=8'h00) |-> result == (a / b) );

  // Division-by-zero handling: allow only X on result in this case
  a_div0_only_x: assert property ( known_inputs() && op==2'b11 && (b==8'h00) |-> $isunknown(result) );
  a_no_x_when_legal: assert property ( known_inputs() && !(op==2'b11 && b==8'h00) |-> !$isunknown(result) );

  // Combinational stability: if inputs didn’t change, result shouldn’t change
  a_stable: assert property ( $stable({a,b,op}) |-> $stable(result) );

  // Functional coverage: each op, div legal/illegal, and overflow/underflow scenarios
  c_add:  cover property ( known_inputs() && op==2'b00 );
  c_sub:  cover property ( known_inputs() && op==2'b01 );
  c_mul:  cover property ( known_inputs() && op==2'b10 );
  c_div:  cover property ( known_inputs() && op==2'b11 && b!=8'h00 );
  c_div0: cover property ( op==2'b11 && b==8'h00 );

  // Interesting arithmetic corners
  c_add_overflow: cover property ( known_inputs() && op==2'b00 && ({1'b0,a}+{1'b0,b})[8] );
  c_sub_underflow: cover property ( known_inputs() && op==2'b01 && (a < b) );
  c_mul_overflow: cover property ( known_inputs() && op==2'b10 && ((a*b)>>8)!=0 );
endmodule

// Example bind (ensure 'clk' is visible in the bind scope)
bind calculator calculator_sva u_calculator_sva (.clk(clk), .a(a), .b(b), .op(op), .result(result));