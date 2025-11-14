// SVA for sky130_fd_sc_hd__nand3
module sky130_fd_sc_hd__nand3_sva (input logic A, B, C, Y);

  // Functional correctness (4-state exact)
  assert property (@(A or B or C or Y) Y === ~(A & B & C))
    else $error("NAND3 mismatch: Y=%b A=%b B=%b C=%b", Y, A, B, C);

  // Output known when inputs are all known
  assert property (@(A or B or C) !$isunknown({A,B,C}) |-> !$isunknown(Y))
    else $error("Known inputs should yield known Y");

  // Output never high-Z
  assert property (@(A or B or C or Y) Y !== 1'bz)
    else $error("Y must never be Z");

  // Controlling-0 dominance (redundant but explicit)
  assert property (@(A or B or C) (A===1'b0 || B===1'b0 || C===1'b0) |-> (Y===1'b1))
    else $error("Controlling-0 violated");

  // Full functional coverage of all input combos (and expected Y)
  cover property (@(A or B or C) A===0 && B===0 && C===0 && Y===1);
  cover property (@(A or B or C) A===0 && B===0 && C===1 && Y===1);
  cover property (@(A or B or C) A===0 && B===1 && C===0 && Y===1);
  cover property (@(A or B or C) A===0 && B===1 && C===1 && Y===1);
  cover property (@(A or B or C) A===1 && B===0 && C===0 && Y===1);
  cover property (@(A or B or C) A===1 && B===0 && C===1 && Y===1);
  cover property (@(A or B or C) A===1 && B===1 && C===0 && Y===1);
  cover property (@(A or B or C) A===1 && B===1 && C===1 && Y===0);

  // Toggle coverage
  cover property (@(A or B or C) $rose(Y));
  cover property (@(A or B or C) $fell(Y));
  cover property (@(A) $rose(A)); cover property (@(A) $fell(A));
  cover property (@(B) $rose(B)); cover property (@(B) $fell(B));
  cover property (@(C) $rose(C)); cover property (@(C) $fell(C));

endmodule

bind sky130_fd_sc_hd__nand3 sky130_fd_sc_hd__nand3_sva u_sky130_fd_sc_hd__nand3_sva (.A(A), .B(B), .C(C), .Y(Y));