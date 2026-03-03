// SVA for calculator. Bind this module to the DUT and drive clk in TB.
// Example: bind calculator calculator_sva u_calc_sva(.clk(tb_clk), .a(a), .b(b), .op(op), .result(result), .valid(valid));

module calculator_sva(
  input logic              clk,
  input logic [7:0]        a, b,
  input logic [1:0]        op,
  input logic [7:0]        result,
  input logic              valid
);
  default clocking cb @(posedge clk); endclocking

  // 8-bit modular arithmetic helpers
  let add8 = (a + b) & 8'hFF;
  let sub8 = (a - b) & 8'hFF;
  let mul8 = (a * b) & 8'hFF;

  // No X on outputs when inputs are known
  assert property ( !$isunknown({a,b,op}) |-> !$isunknown({result,valid}) );

  // Valid definition (only low on divide-by-zero)
  assert property ( !$isunknown({a,b,op}) |-> (valid == !(op==2'b11 && b==8'h00)) );

  // Result correctness per operation
  assert property ( !$isunknown({a,b,op}) && op==2'b00 |-> result == add8 );
  assert property ( !$isunknown({a,b,op}) && op==2'b01 |-> result == sub8 );
  assert property ( !$isunknown({a,b,op}) && op==2'b10 |-> result == mul8 );
  assert property ( !$isunknown({a,b,op}) && op==2'b11 && b!=8'h00 |-> result == (a / b) );
  assert property ( !$isunknown({a,b,op}) && op==2'b11 && b==8'h00 |-> result == 8'h00 && valid==1'b0 );

  // Op encoding must be known
  assert property ( !$isunknown(op) );

  // Functional coverage
  cover property ( !$isunknown({a,b,op}) && op==2'b00 );
  cover property ( !$isunknown({a,b,op}) && op==2'b01 );
  cover property ( !$isunknown({a,b,op}) && op==2'b10 );
  cover property ( !$isunknown({a,b,op}) && op==2'b11 );
  cover property ( !$isunknown({a,b,op}) && op==2'b11 && b==8'h00 );           // divide-by-zero
  cover property ( !$isunknown({a,b,op}) && op==2'b00 && ((a + b) > 9'h0FF) ); // add overflow
  cover property ( !$isunknown({a,b,op}) && op==2'b01 && (a < b) );            // sub underflow
  cover property ( !$isunknown({a,b,op}) && op==2'b10 && ((a * b) > 16'h00FF) ); // mul overflow
  cover property ( !$isunknown({a,b,op}) && op==2'b11 && b!=8'h00 && (a < b) );  // div zero-quotient
  cover property ( !$isunknown({a,b,op}) && op==2'b11 && b!=8'h00 && ((a % b) == 0) ); // exact division
endmodule