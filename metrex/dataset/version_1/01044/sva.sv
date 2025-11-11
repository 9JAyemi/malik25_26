// SVA for sky130_fd_sc_ms__a2111o
// Clocked concurrent assertions; bind this to the DUT and supply clk/rst_n.

module sky130_fd_sc_ms__a2111o_sva (
  input logic clk,
  input logic rst_n,

  input logic X,
  input logic A1,
  input logic A2,
  input logic B1,
  input logic C1,
  input logic D1,
  input logic VPWR,
  input logic VGND,
  input logic VPB,
  input logic VNB
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // Exact-match predicates for early selects
  logic e1 = (A1===1'b1 && A2===1'b0);
  logic e2 = (A1===1'b0 && A2===1'b1);
  logic e3 = (A1===1'b1 && A2===1'b1);
  logic e4 = (A1===1'b0 && A2===1'b0);
  logic pre0 = !(e1 || e2 || e3 || e4);

  // Exact 1/0 checks for later priority chain
  logic b1 = (B1===1'b1), b0 = (B1===1'b0);
  logic c1 = (C1===1'b1), c0 = (C1===1'b0);
  logic d1 = (D1===1'b1), d0 = (D1===1'b0);
  logic p1 = (VPWR===1'b1), p0 = (VPWR===1'b0);
  logic g1 = (VGND===1'b1), g0 = (VGND===1'b0);
  logic pb1 = (VPB===1'b1), pb0 = (VPB===1'b0);
  logic nb1 = (VNB===1'b1), nb0 = (VNB===1'b0);

  // Core functional spec (with known A2, output is ~A2, independent of other pins)
  assert property (!$isunknown(A2) |-> (X === ~A2));

  // Early explicit cases (redundant with above but good for coverage/debug clarity)
  assert property (e1 |-> X===1'b1);
  assert property (e2 |-> X===1'b0);
  assert property (e3 |-> X===1'b0);
  assert property (e4 |-> X===1'b1);

  // Priority chain under unknown A1/A2, requiring strict bypass of earlier terms
  assert property (pre0 && b1                               |-> X===1'b0);
  assert property (pre0 && b0 && c1                         |-> X===1'b1);
  assert property (pre0 && b0 && c0 && d1                   |-> X===1'b0);
  assert property (pre0 && b0 && c0 && d0 && p1             |-> X===1'b1);
  assert property (pre0 && b0 && c0 && d0 && p0 && g1       |-> X===1'b0);
  assert property (pre0 && b0 && c0 && d0 && p0 && g0 && pb1|-> X===1'b0);
  assert property (pre0 && b0 && c0 && d0 && p0 && g0 && pb0 && nb1 |-> X===1'b1);
  assert property (pre0 && b0 && c0 && d0 && p0 && g0 && pb0 && nb0 |-> X===1'b0);

  // Determinism when all inputs are 0/1
  assert property (!$isunknown({A1,A2,B1,C1,D1,VPWR,VGND,VPB,VNB}) |-> !$isunknown(X));

  // Coverage
  cover property ($fell(A2) && !$isunknown(A2) && X===1'b1);
  cover property ($rose(A2) && !$isunknown(A2) && X===1'b0);

  cover property (pre0 && b1);
  cover property (pre0 && b0 && c1);
  cover property (pre0 && b0 && c0 && d1);
  cover property (pre0 && b0 && c0 && d0 && p1);
  cover property (pre0 && b0 && c0 && d0 && p0 && g1);
  cover property (pre0 && b0 && c0 && d0 && p0 && g0 && pb1);
  cover property (pre0 && b0 && c0 && d0 && p0 && g0 && pb0 && nb1);
  cover property (pre0 && b0 && c0 && d0 && p0 && g0 && pb0 && nb0);
endmodule

// Example bind (edit clk/rst_n as appropriate):
// bind sky130_fd_sc_ms__a2111o sky130_fd_sc_ms__a2111o_sva u_sva (.* , .clk(tb_clk), .rst_n(tb_rst_n));