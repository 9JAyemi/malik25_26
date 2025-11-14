// SVA checker for add_sub_4bit
module add_sub_4bit_sva(
  input  logic [3:0] A,
  input  logic [3:0] B,
  input  logic       mode,
  input  logic       cin,
  input  logic [3:0] sum,
  input  logic       cout
);
  // Sample on any input change; ignore checks when inputs are X/Z
  default clocking cb @(A or B or mode or cin); endclocking
  default disable iff ($isunknown({A,B,mode,cin}));

  // Correctness: 5-bit result must match true arithmetic (carry/borrow in MSB)
  assert property ( (mode==1'b0) |-> ({cout,sum} == ({1'b0,A} + {1'b0,B} + cin)) )
    else $error("ADD mismatch: A=%0h B=%0h cin=%0b -> sum=%0h cout=%0b", A,B,cin,sum,cout);

  assert property ( (mode==1'b1) |-> ({cout,sum} == ({1'b0,A} - {1'b0,B} - cin)) )
    else $error("SUB mismatch: A=%0h B=%0h cin=%0b -> sum=%0h cout=%0b", A,B,cin,sum,cout);

  // Outputs must be known when inputs are known
  assert property (!$isunknown({sum,cout}))
    else $error("Outputs X/Z with known inputs");

  // Minimal functional coverage
  cover property (mode==0 && cin==0);
  cover property (mode==0 && cin==1);
  cover property (mode==1 && cin==0);
  cover property (mode==1 && cin==1);
  cover property ((mode==0) && (({1'b0,A}+{1'b0,B}+cin)[4] == 1'b1)); // add carry-out
  cover property ((mode==1) && (({1'b0,A}-{1'b0,B}-cin)[4] == 1'b1)); // sub borrow-out
  cover property (sum==4'h0);
  cover property ((mode==1) && (A==B) && (cin==0)); // exact zero result, no borrow
endmodule

bind add_sub_4bit add_sub_4bit_sva sva_i (.*);