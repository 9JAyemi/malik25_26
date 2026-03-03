// SVA for module arithmetic
`ifndef ARITHMETIC_SVA_SV
`define ARITHMETIC_SVA_SV

module arithmetic_sva (
  input logic [7:0] a,
  input logic [7:0] b,
  input logic [2:0] ctrl,
  input logic [7:0] z
);
  // Disable checks if inputs are X/Z; use ##0 to sample after combinational settle
  default disable iff ($isunknown({a,b,ctrl}));

  // Functional correctness per opcode
  assert property ( (ctrl==3'b000) |-> ##0 (z === (a + b)) ) else $error("ADD mismatch");
  assert property ( (ctrl==3'b001) |-> ##0 (z === (a - b)) ) else $error("SUB mismatch");
  assert property ( (ctrl==3'b010) |-> ##0 (z === (a * b)[7:0]) ) else $error("MUL LSB mismatch");
  assert property ( (ctrl==3'b101) |-> ##0 (z === (a & b)) ) else $error("AND mismatch");
  assert property ( (ctrl==3'b110) |-> ##0 (z === (a | b)) ) else $error("OR mismatch");
  assert property ( (ctrl==3'b111) |-> ##0 (z === (a ^ b)) ) else $error("XOR mismatch");

  // Division/remainder semantics (incl. divide-by-zero behavior)
  assert property ( (ctrl==3'b011) && (b!=0) |-> ##0 (z === (a / b)) ) else $error("DIV mismatch");
  assert property ( (ctrl==3'b011) && (b==0) |-> ##0 $isunknown(z) ) else $error("DIV by zero should produce X");
  assert property ( (ctrl==3'b100) && (b!=0) |-> ##0 (z === (a % b)) ) else $error("REM mismatch");
  assert property ( (ctrl==3'b100) && (b!=0) |-> ##0 (z < b) ) else $error("REM out of range");
  assert property ( (ctrl==3'b100) && (b==0) |-> ##0 $isunknown(z) ) else $error("REM by zero should produce X");

  // z should be known on non-div/rem ops when inputs known
  assert property ( (ctrl inside {3'b000,3'b001,3'b010,3'b101,3'b110,3'b111}) |-> ##0 !$isunknown(z) )
    else $error("z unknown on non-div/rem op");

  // Algebraic consistency when b!=0: a == (a/b)*b + (a%b)
  assert property ( (b!=0) |-> ##0 ($unsigned(a) == $unsigned(a/b)*$unsigned(b) + $unsigned(a%b)) )
    else $error("a != q*b + r");
  // Coverage: each opcode + key corner cases
  cover property (ctrl==3'b000);
  cover property (ctrl==3'b001);
  cover property (ctrl==3'b010);
  cover property (ctrl==3'b011);
  cover property (ctrl==3'b100);
  cover property (ctrl==3'b101);
  cover property (ctrl==3'b110);
  cover property (ctrl==3'b111);

  cover property ( (ctrl==3'b000) && ((a + b) < a) );                 // add overflow wrap
  cover property ( (ctrl==3'b001) && (a < b) );                        // sub underflow wrap
  cover property ( (ctrl==3'b010) && (((a * b) >> 8) != 0) );          // mul overflow
  cover property ( (ctrl==3'b011) && (b == 0) );                       // div by zero
  cover property ( (ctrl==3'b100) && (b == 0) );                       // rem by zero
endmodule

bind arithmetic arithmetic_sva i_arithmetic_sva (.a(a), .b(b), .ctrl(ctrl), .z(z));

`endif