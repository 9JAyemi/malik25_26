// Drop this SVA block inside module xor3 (after gate instantiations)

`ifndef SYNTHESIS
// Sample on any relevant edge and ignore X/Z while checking
default clocking cb @(
  posedge A or negedge A or
  posedge B or negedge B or
  posedge C or negedge C or
  posedge nand1_out or negedge nand1_out or
  posedge nand2_out or negedge nand2_out or
  posedge Y or negedge Y
); endclocking
default disable iff ($isunknown({A,B,C,nand1_out,nand2_out,Y}));

function automatic logic y_ref(logic a,b,c);
  return (~(a & b)) & c;
endfunction

// Gate-level correctness
assert property (1'b1 |-> ##0 (nand1_out === ~(A & B))) else $error("nand1_out != ~(A&B)");
assert property (1'b1 |-> ##0 (nand2_out === ~(nand1_out & C))) else $error("nand2_out != ~(nand1_out&C)");
assert property (1'b1 |-> ##0 (Y === ~nand2_out)) else $error("Y != ~nand2_out");

// End-to-end function
assert property (1'b1 |-> ##0 (Y === y_ref(A,B,C))) else $error("Y functional mismatch");

// Output known when inputs known
assert property (!$isunknown({A,B,C}) |-> ##0 !$isunknown(Y)) else $error("Y is X/Z with known inputs");

// Full input-space coverage (with expected Y)
cover property (##0 (A==0 && B==0 && C==0 && Y==0));
cover property (##0 (A==0 && B==0 && C==1 && Y==1));
cover property (##0 (A==0 && B==1 && C==0 && Y==0));
cover property (##0 (A==0 && B==1 && C==1 && Y==1));
cover property (##0 (A==1 && B==0 && C==0 && Y==0));
cover property (##0 (A==1 && B==0 && C==1 && Y==1));
cover property (##0 (A==1 && B==1 && C==0 && Y==0));
cover property (##0 (A==1 && B==1 && C==1 && Y==0));

// Toggle coverage on internal nodes and output
cover property ($rose(nand1_out)); cover property ($fell(nand1_out));
cover property ($rose(nand2_out)); cover property ($fell(nand2_out));
cover property ($rose(Y));         cover property ($fell(Y));
`endif