// SVA for add_sub. Bind or instantiate with a sampling clock and reset.

module add_sub_sva (
  input  logic        clk,
  input  logic        rst_n,
  input  logic [3:0]  a,
  input  logic [3:0]  b,
  input  logic        sub,
  input  logic        cin,
  input  logic        cout,
  input  logic        overflow,
  input  logic [3:0]  sum
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n)

  // Helpers
  function automatic logic [4:0] add5(input logic [3:0] x, y, input logic c);
    return {1'b0,x} + {1'b0,y} + c;
  endfunction
  function automatic logic [4:0] sub5(input logic [3:0] x, y, input logic c);
    return {1'b0,x} - {1'b0,y} - c;
  endfunction
  function automatic logic borrow(input logic [3:0] x, y, input logic c);
    return ({1'b0,x} < ({1'b0,y} + c));
  endfunction

  // No X/Z on outputs when inputs are known
  assert property (!$isunknown({a,b,sub,cin}) |-> !$isunknown({sum,cout,overflow})) else $error("X/Z on outputs");

  // Purely combinational behavior (no memory)
  assert property ($stable({a,b,sub,cin}) |-> $stable({sum,cout,overflow})) else $error("Outputs change without input change");

  // Addition mode checks
  assert property (!sub |-> sum == add5(a,b,cin)[3:0]) else $error("ADD sum mismatch");
  assert property (!sub |-> cout == add5(a,b,cin)[4])   else $error("ADD cout mismatch");
  assert property (!sub |-> overflow == add5(a,b,cin)[4]) else $error("ADD overflow mismatch");

  // Subtraction mode checks (unsigned borrow semantics)
  assert property ( sub |-> sum == sub5(a,b,cin)[3:0])   else $error("SUB sum mismatch");
  assert property ( sub |-> cout == borrow(a,b,cin))     else $error("SUB cout (borrow) mismatch");
  assert property ( sub |-> overflow == borrow(a,b,cin)) else $error("SUB overflow (borrow) mismatch");

  // Basic functional coverage
  cover property (!sub && add5(a,b,cin) <= 5'd15);   // add no carry
  cover property (!sub && add5(a,b,cin) >  5'd15);   // add carry
  cover property ( sub && !borrow(a,b,cin));         // sub no borrow
  cover property ( sub &&  borrow(a,b,cin));         // sub borrow
  cover property (!sub ##1 sub);                     // switch add->sub
  cover property ( sub ##1 !sub);                    // switch sub->add
  cover property (!sub && a==4'hF && b==4'hF && cin); // add max + carry-in
  cover property ( sub && a==4'h0 && b==4'hF && cin); // sub min - max - cin

endmodule

// Example bind (provide clk and rst_n from your environment):
// bind add_sub add_sub_sva u_add_sub_sva(.clk(clk), .rst_n(rst_n),
//   .a(a), .b(b), .sub(sub), .cin(cin), .cout(cout), .overflow(overflow), .sum(sum));