// SVA checker for tri_buf
// Binds to the DUT and verifies combinational correctness and key use-cases.

module tri_buf_sva (
  input logic A,
  input logic Z,
  input logic TE_B
);
  default clocking cb @(*); endclocking

  // Functional equivalence (4-state accurate)
  ap_eq: assert property (Z === (TE_B ? 1'b0 : A))
    else $error("tri_buf: Z != (TE_B ? 1'b0 : A)");

  // Useful scenario coverage
  cp_force0:  cover property (TE_B === 1'b1 && Z === 1'b0);
  cp_pass0:   cover property (TE_B === 1'b0 && A === 1'b0 && Z === 1'b0);
  cp_pass1:   cover property (TE_B === 1'b0 && A === 1'b1 && Z === 1'b1);

  // Toggle coverage
  cp_A_toggle_enabled: cover property (TE_B === 1'b0 && $changed(A) && Z === A);
  cp_TE_B_lo_to_hi:    cover property ($rose(TE_B) && Z === 1'b0);
  cp_TE_B_hi_to_lo:    cover property ($fell(TE_B) && Z === A);

  // Optional: observe Z propagates Z when A is Z and enabled
  cp_highz_pass: cover property (TE_B === 1'b0 && A === 1'bz && Z === 1'bz);
endmodule

// Bind into the DUT
bind tri_buf tri_buf_sva u_tri_buf_sva (.A(A), .Z(Z), .TE_B(TE_B));