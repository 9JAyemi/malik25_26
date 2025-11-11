// SVA for sky130_fd_sc_hdll__a222oi
// Function: Y = ~((A1&A2) | (B1&B2) | (C1&C2))

bind sky130_fd_sc_hdll__a222oi sky130_fd_sc_hdll__a222oi_sva a222oi_sva();

module sky130_fd_sc_hdll__a222oi_sva;

  // Sample on any input change
  default clocking cb @(A1 or A2 or B1 or B2 or C1 or C2); endclocking

  // Functional equivalence (4-state accurate)
  a_func: assert property (
    Y === ~((A1 & A2) | (B1 & B2) | (C1 & C2))
  ) else $error("a222oi func mismatch: Y != ~((A1&A2)|(B1&B2)|(C1&C2))");

  // Structural checks (internal nets)
  a_nand0: assert property (nand0_out   === ~(A1 & A2))
    else $error("nand0 mismatch");
  a_nand1: assert property (nand1_out   === ~(B1 & B2))
    else $error("nand1 mismatch");
  a_nand2: assert property (nand2_out   === ~(C1 & C2))
    else $error("nand2 mismatch");
  a_and0 : assert property (and0_out_Y  === (nand0_out & nand1_out & nand2_out))
    else $error("and0 mismatch");
  a_buf0 : assert property (Y === and0_out_Y)
    else $error("buf0 mismatch");

  // Basic functional coverage
  c_y1: cover property (Y == 1);
  c_y0: cover property (Y == 0);

  // Corner cases: exactly which pair(s) force low
  c_Apair_low: cover property ((A1 & A2) && (Y == 0));
  c_Bpair_low: cover property ((B1 & B2) && (Y == 0));
  c_Cpair_low: cover property ((C1 & C2) && (Y == 0));

  // No pair asserted -> output high
  c_no_pairs: cover property (!(A1 & A2) && !(B1 & B2) && !(C1 & C2) && (Y == 1));

  // Multiple pairs asserted -> still low
  c_two_AB:   cover property ((A1 & A2) && (B1 & B2) && (Y == 0));
  c_two_AC:   cover property ((A1 & A2) && (C1 & C2) && (Y == 0));
  c_two_BC:   cover property ((B1 & B2) && (C1 & C2) && (Y == 0));
  c_all_three:cover property ((A1 & A2) && (B1 & B2) && (C1 & C2) && (Y == 0));

  // Optional X-behavior coverage
  c_x: cover property ($isunknown({A1,A2,B1,B2,C1,C2}) && $isunknown(Y));

endmodule