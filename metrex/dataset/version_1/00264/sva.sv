// SVA for and_nand: concise, full functional/structural checks + key coverage

module and_nand_sva (
  input logic A,
  input logic B,
  input logic Y,
  input logic nand1,
  input logic nand2,
  input logic nand3
);
  default clocking cb @(*); endclocking

  // Functional correctness (4-state exact)
  assert property (Y === (A & B))
    else $error("Y != A & B (4-state)");


  // Structural chain checks (4-state exact)
  assert property (nand1 === ~(A & B))
    else $error("nand1 != ~(A & B)");
  assert property (nand2 === ~nand1)
    else $error("nand2 != ~nand1");
  assert property (nand3 === ~nand2)
    else $error("nand3 != ~nand2");
  assert property (Y     === ~nand3)
    else $error("Y != ~nand3");


  // Input-space coverage (all 4 combos with expected Y)
  cover property (A==0 && B==0 && Y==0);
  cover property (A==0 && B==1 && Y==0);
  cover property (A==1 && B==0 && Y==0);
  cover property (A==1 && B==1 && Y==1);

  // Basic toggle coverage on output
  cover property ($rose(Y));
  cover property ($fell(Y));
endmodule


// Bind into the DUT to access internals
bind and_nand and_nand_sva sva_and_nand (
  .A(A),
  .B(B),
  .Y(Y),
  .nand1(nand1),
  .nand2(nand2),
  .nand3(nand3)
);