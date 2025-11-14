// SVA for arithmetic. Bind this to the DUT and provide clk/rst_n from your environment.
module arithmetic_sva #(parameter int WIDTH = 8)
(
  input logic                     clk,
  input logic                     rst_n,
  input logic [WIDTH-1:0]         a,
  input logic [WIDTH-1:0]         b,
  input logic [WIDTH-1:0]         result
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // No X/Z on output when inputs are known
  assert property ( (!$isunknown({a,b})) |-> !$isunknown(result) );

  // Exactly one relational condition holds when inputs are known
  assert property ( (!$isunknown({a,b})) |-> $onehot({a>b, a<b, a==b}) );

  // Functional equivalence (golden reference)
  assert property ( result == ( (a>b) ? (a+b)
                                   : (a<b) ? (a-b)
                                           : (a & b) ) );

  // Branch-specific correctness (also aids debug/coverage)
  assert property ( (a>b)  |-> result == a+b );
  assert property ( (a<b)  |-> result == a-b );
  assert property ( (a==b) |-> result == (a & b) );

  // Branch coverage
  cover property ( (a>b)  && result == a+b );
  cover property ( (a<b)  && result == a-b );
  cover property ( (a==b) && result == (a & b) );

  // Corner-case coverage
  cover property ( (a>b) && ((a+b) < a) );  // add overflow wrap
  cover property ( (a<b) && ((a-b) > a) );  // sub underflow wrap
  cover property ( a==WIDTH'(0)   && b==WIDTH'(0)   );
  cover property ( a=={WIDTH{1'b1}} && b=={WIDTH{1'b1}} );
  cover property ( a=={WIDTH{1'b1}} && b==WIDTH'(0) );
  cover property ( a==WIDTH'(0)     && b=={WIDTH{1'b1}} );

endmodule

// Example bind (provide clk/rst_n from your env)
// bind arithmetic arithmetic_sva #(.WIDTH(8))) u_arithmetic_sva (.* , .clk(clk), .rst_n(rst_n));