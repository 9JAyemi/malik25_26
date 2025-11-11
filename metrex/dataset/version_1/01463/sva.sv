// SVA for fourBitAdder
// Concise, high-quality checks and coverage for a pure combinational adder.

`ifndef FOUR_BIT_ADDER_SVA
`define FOUR_BIT_ADDER_SVA

module fourBitAdder_sva (
  input  [3:0] A,
  input  [3:0] B,
  input        Cin,
  input  [3:0] Sum,
  input        Cout
);

  // Correctness: outputs equal 5-bit addition (allow delta to settle)
  assert property (@(A or B or Cin) !$isunknown({A,B,Cin}) |-> ##0 {Cout,Sum} == A + B + Cin)
    else $error("fourBitAdder: result mismatch");

  // No unknowns on outputs when inputs are known
  assert property (@(A or B or Cin) !$isunknown({A,B,Cin}) |-> ##0 !$isunknown({Sum,Cout}))
    else $error("fourBitAdder: X/Z on outputs with known inputs");

  // Pure combinational behavior: outputs don’t change unless inputs do
  assert property (@(A or B or Cin or Sum or Cout) $stable({A,B,Cin}) |-> ##0 $stable({Sum,Cout}))
    else $error("fourBitAdder: outputs changed without input change");

  // Functional coverage: key scenarios
  // No carry, Cin=0
  cover property (@(A or B or Cin) ##0 (Cin==0 && (A+B) < 16 && Cout==0));
  // Generate carry with Cin=0
  cover property (@(A or B or Cin) ##0 (Cin==0 && (A+B) >= 16 && Cout==1));
  // Propagate carry: A+B==15 and Cin=1 -> Sum==0, Cout==1
  cover property (@(A or B or Cin) ##0 (Cin==1 && (A+B)==15 && Sum==4'h0 && Cout==1));
  // Kill carry: A+B==0 and Cin=1 -> Sum==1, Cout==0
  cover property (@(A or B or Cin) ##0 (Cin==1 && (A+B)==0  && Sum==4'h1 && Cout==0));

endmodule

bind fourBitAdder fourBitAdder_sva sva_i (.*);

`endif