// SVA for sky130_fd_sc_hd__nand4b (Y = ~(D & C & B & ~A_N) = A_N | ~B | ~C | ~D)
`ifndef SKY130_FD_SC_HD__NAND4B_SVA
`define SKY130_FD_SC_HD__NAND4B_SVA

module sky130_fd_sc_hd__nand4b_sva
(
  input logic Y,
  input logic A_N,
  input logic B,
  input logic C,
  input logic D
);
  default clocking cb @(*); endclocking

  // Core functional check (4-state accurate), allow ##0 settle in same timestep
  assert property (1'b1 |-> ##0 (Y === ~(D & C & B & ~A_N)));

  // Deterministic when inputs are known
  assert property ((!$isunknown({A_N,B,C,D})) |-> ##0 (! $isunknown(Y) && (Y == (A_N | ~B | ~C | ~D))));

  // Controlling values must force Y=1
  assert property (A_N === 1'b1 |-> ##0 Y === 1'b1);
  assert property (B   === 1'b0 |-> ##0 Y === 1'b1);
  assert property (C   === 1'b0 |-> ##0 Y === 1'b1);
  assert property (D   === 1'b0 |-> ##0 Y === 1'b1);

  // Only way to get Y=0
  assert property (Y === 1'b0 |-> (A_N === 1'b0 && B === 1'b1 && C === 1'b1 && D === 1'b1));

  // Reduction when A_N=0 => 3-input NAND of B,C,D
  assert property (A_N === 1'b0 |-> ##0 (Y === ~(B & C & D)));

  // When B=C=D=1, Y tracks A_N
  assert property ((B===1'b1 && C===1'b1 && D===1'b1) |-> ##0 (Y === A_N));

  // Output knownness on low (implied by only-zero case)
  assert property (Y === 1'b0 |-> ! $isunknown({A_N,B,C,D}));

  // Truth-table coverage: hit all 16 input combinations
  genvar gi;
  for (gi=0; gi<16; gi++) begin : tt_cov
    localparam logic [3:0] COMBO = gi[3:0];
    cover property (##0 ({A_N,B,C,D} === COMBO));
  end

  // Output level and transitions coverage (with known signals)
  cover property (! $isunknown({A_N,B,C,D,Y}) && Y===1'b0);
  cover property (! $isunknown({A_N,B,C,D,Y}) && Y===1'b1);
  cover property (! $isunknown({A_N,B,C,D,Y}) && $rose(Y));
  cover property (! $isunknown({A_N,B,C,D,Y}) && $fell(Y));

endmodule

// Bind into the DUT
bind sky130_fd_sc_hd__nand4b sky130_fd_sc_hd__nand4b_sva nand4b_sva_i (
  .Y(Y), .A_N(A_N), .B(B), .C(C), .D(D)
);

`endif