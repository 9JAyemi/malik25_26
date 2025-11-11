// SVA for sky130_fd_sc_ls__nand2
// Bind this file alongside the DUT

module sky130_fd_sc_ls__nand2_sva (
  input logic A,
  input logic B,
  input logic Y
);
  default clocking cb @(*); endclocking

  // Functional equivalence (4-state accurate)
  assert property (Y === ~(A & B))
    else $error("NAND mismatch: Y != ~(A & B)");

  // Deterministic truth-table corners
  assert property ((A===1'b0 || B===1'b0) |-> Y===1'b1)
    else $error("NAND: expected Y=1 when any input is 0");
  assert property ((A===1'b1 && B===1'b1) |-> Y===1'b0)
    else $error("NAND: expected Y=0 when A=B=1");
  assert property (Y===1'b0 |-> (A===1'b1 && B===1'b1))
    else $error("NAND: Y=0 implies A=B=1");

  // X/Z handling
  assert property ((!$isunknown({A,B})) |-> !$isunknown(Y))
    else $error("NAND: known inputs must yield known Y");
  assert property ((A===1'b1 && $isunknown(B)) |-> $isunknown(Y))
    else $error("NAND: A=1 and B unknown must yield Y unknown");
  assert property ((B===1'b1 && $isunknown(A)) |-> $isunknown(Y))
    else $error("NAND: B=1 and A unknown must yield Y unknown");

  // Edge responses (combinational, zero-delay semantics)
  assert property ($rose(A) && B===1'b1 |-> $fell(Y))
    else $error("NAND: A rise with B=1 must make Y fall");
  assert property ($rose(B) && A===1'b1 |-> $fell(Y))
    else $error("NAND: B rise with A=1 must make Y fall");
  assert property ($fell(A) |-> Y===1'b1)
    else $error("NAND: A fall must drive Y=1");
  assert property ($fell(B) |-> Y===1'b1)
    else $error("NAND: B fall must drive Y=1");

  // Basic functional coverage
  cover property (A===1'b0 && B===1'b0 && Y===1'b1);
  cover property (A===1'b0 && B===1'b1 && Y===1'b1);
  cover property (A===1'b1 && B===1'b0 && Y===1'b1);
  cover property (A===1'b1 && B===1'b1 && Y===1'b0);

  // Edge/toggle coverage
  cover property ($rose(A) && B===1'b1 ##0 $fell(Y));
  cover property ($rose(B) && A===1'b1 ##0 $fell(Y));
  cover property ($fell(A) ##0 (Y===1'b1));
  cover property ($fell(B) ##0 (Y===1'b1));

  // X-propagation coverage
  cover property (A===1'b1 && $isunknown(B) && $isunknown(Y));
  cover property (B===1'b1 && $isunknown(A) && $isunknown(Y));
endmodule

bind sky130_fd_sc_ls__nand2 sky130_fd_sc_ls__nand2_sva nand2_sva_bind (.A(A), .B(B), .Y(Y));