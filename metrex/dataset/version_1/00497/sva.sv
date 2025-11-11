// SVA for sky130_fd_sc_ls__nand4bb
`ifndef SKY130_FD_SC_LS__NAND4BB_SVA
`define SKY130_FD_SC_LS__NAND4BB_SVA

module sky130_fd_sc_ls__nand4bb_sva;

  // Functional equivalence
  assert property (@(A_N or B_N or C or D or nand0_out or or0_out_Y or Y)
                   Y === (A_N | B_N | ~(C & D)));

  // Knownness: all-known inputs -> known output
  assert property (@(A_N or B_N or C or D)
                   !$isunknown({A_N,B_N,C,D}) |-> !$isunknown(Y));

  // Dominating values
  assert property (@(A_N) A_N === 1'b1 |-> Y === 1'b1);
  assert property (@(B_N) B_N === 1'b1 |-> Y === 1'b1);
  assert property (@(C)  C  === 1'b0 |-> Y === 1'b1);
  assert property (@(D)  D  === 1'b0 |-> Y === 1'b1);

  // Unique low condition
  assert property (@(A_N or B_N or C or D)
                   (A_N===1'b0 && B_N===1'b0 && C===1'b1 && D===1'b1) |-> Y===1'b0);
  assert property (@(A_N or B_N or C or D)
                   Y===1'b0 |-> (A_N===1'b0 && B_N===1'b0 && C===1'b1 && D===1'b1));

  // Structural consistency of internal nets
  assert property (@(C or D)                     nand0_out  === ~(C & D));
  assert property (@(A_N or B_N or nand0_out)    or0_out_Y  === (A_N | B_N | nand0_out));
  assert property (@(or0_out_Y or Y)             Y          === or0_out_Y);

  // Coverage: output toggles
  cover property (@(A_N or B_N or C or D) $rose(Y));
  cover property (@(A_N or B_N or C or D) $fell(Y));

  // Coverage: each dominant cause for Y==1
  cover property (@(A_N or B_N or C or D) (A_N===1 && B_N===0 && C===1 && D===1 && Y===1));
  cover property (@(A_N or B_N or C or D) (A_N===0 && B_N===1 && C===1 && D===1 && Y===1));
  cover property (@(A_N or B_N or C or D) (A_N===0 && B_N===0 && C===0 && D===1 && Y===1));
  cover property (@(A_N or B_N or C or D) (A_N===0 && B_N===0 && C===1 && D===0 && Y===1));

  // Coverage: unique low vector
  cover property (@(A_N or B_N or C or D) (A_N===0 && B_N===0 && C===1 && D===1 && Y===0));

endmodule

bind sky130_fd_sc_ls__nand4bb sky130_fd_sc_ls__nand4bb_sva sva_i();

`endif