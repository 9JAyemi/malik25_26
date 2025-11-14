// SVA for Arithmetic_Logic_Operations
module Arithmetic_Logic_Operations_sva (
  input logic [7:0] a,
  input logic [7:0] b,
  input logic [2:0] op,
  input logic       sel,
  input logic [7:0] out,
  input logic [7:0] result
);
  default clocking cb @(*); endclocking

  // No-X propagation when inputs are known
  assert property (disable iff ($isunknown({a,b,op,sel})))
    ##0 !$isunknown({result,out});

  // Functional correctness of result for each op
  assert property (disable iff ($isunknown({a,b,op}))) (op==3'b000) |-> ##0 (result == (a + b));   // add
  assert property (disable iff ($isunknown({a,b,op}))) (op==3'b001) |-> ##0 (result == (a - b));   // sub
  assert property (disable iff ($isunknown({a,b,op}))) (op==3'b010) |-> ##0 (result == (a & b));   // and
  assert property (disable iff ($isunknown({a,b,op}))) (op==3'b011) |-> ##0 (result == (a | b));   // or
  assert property (disable iff ($isunknown({a,b,op}))) (op==3'b100) |-> ##0 (result == (a ^ b));   // xor
  assert property (disable iff ($isunknown({a,op})))   (op==3'b101) |-> ##0 (result == (~a));      // not
  assert property (disable iff ($isunknown({a,b,op}))) (op==3'b110) |-> ##0 (result == (a << b));  // shl
  assert property (disable iff ($isunknown({a,b,op}))) (op==3'b111) |-> ##0 (result == (a >> b));  // shr

  // Output select behavior
  assert property (disable iff ($isunknown({a,b,op,sel})))
    1 |-> ##0 (out == (sel ? result : a));

  // Minimal functional coverage
  cover property (op==3'b000);
  cover property (op==3'b001);
  cover property (op==3'b010);
  cover property (op==3'b011);
  cover property (op==3'b100);
  cover property (op==3'b101);
  cover property (op==3'b110);
  cover property (op==3'b111);
  cover property (sel==1'b0);
  cover property (sel==1'b1);

  // Corner-case coverage
  cover property ((op==3'b000) && ((a + b) < a));   // add overflow wrap
  cover property ((op==3'b001) && (a < b));         // sub borrow
  cover property ((op==3'b110) && (b==0));
  cover property ((op==3'b110) && (b>=8));          // shift >= width -> 0
  cover property ((op==3'b111) && (b==0));
  cover property ((op==3'b111) && (b>=8));
endmodule

bind Arithmetic_Logic_Operations Arithmetic_Logic_Operations_sva sva_i (
  .a(a), .b(b), .op(op), .sel(sel), .out(out), .result(result)
);