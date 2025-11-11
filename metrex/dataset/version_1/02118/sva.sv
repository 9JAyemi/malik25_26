// SVA checker for and_gate_ctrl
module and_gate_ctrl_sva (
  input logic A, B, C1, Y
);

  // Sample on any input/output change (combinational block)
  default clocking cb @(A or B or C1 or Y); endclocking

  // Functional equivalence (4-state accurate to ?: semantics)
  assert property (Y === (C1 ? (A & B) : 1'b0))
    else $error("Y != (C1 ? (A & B) : 1'b0)");

  // Safety properties
  assert property ((Y === 1'b1) |-> (C1 === 1'b1 && A === 1'b1 && B === 1'b1))
    else $error("Y is 1 without C1&A&B all 1");
  assert property ((C1 === 1'b0) |-> (Y === 1'b0))
    else $error("C1=0 but Y != 0");
  assert property ((C1 === 1'b1) |-> (Y === (A & B)))
    else $error("C1=1 but Y != A&B");
  // No X on Y when all inputs are known
  assert property (((C1 !== 1'bx) && (A !== 1'bx) && (B !== 1'bx)) |-> (Y !== 1'bx))
    else $error("Y is X while A,B,C1 are all known");

  // Truth-table coverage (all 8 input combinations under correct Y)
  cover property ((C1==0 && A==0 && B==0 && Y==0));
  cover property ((C1==0 && A==0 && B==1 && Y==0));
  cover property ((C1==0 && A==1 && B==0 && Y==0));
  cover property ((C1==0 && A==1 && B==1 && Y==0));
  cover property ((C1==1 && A==0 && B==0 && Y==0));
  cover property ((C1==1 && A==0 && B==1 && Y==0));
  cover property ((C1==1 && A==1 && B==0 && Y==0));
  cover property ((C1==1 && A==1 && B==1 && Y==1));

  // Toggle coverage
  cover property (@(posedge Y) 1'b1);
  cover property (@(negedge Y) 1'b1);

endmodule

// Bind into DUT
bind and_gate_ctrl and_gate_ctrl_sva u_and_gate_ctrl_sva (.A(A), .B(B), .C1(C1), .Y(Y));