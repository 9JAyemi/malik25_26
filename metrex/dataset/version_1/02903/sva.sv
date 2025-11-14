// SVA for sky130_fd_sc_ls__nand4b
// Bind this module to the DUT to check functionality, X-prop, and provide concise coverage.

module sky130_fd_sc_ls__nand4b_sva
(
  input logic Y,
  input logic A_N,
  input logic B,
  input logic C,
  input logic D
);
  // Helper
  wire no_ctrl0 = (A_N !== 1'b1) && (B !== 1'b0) && (C !== 1'b0) && (D !== 1'b0);

  // Core functional equivalence when inputs are known (4-state accurate)
  always @* if (!$isunknown({A_N,B,C,D}))
    assert (#0 (Y === ~(B & C & D & ~A_N)));

  // Dominating 1s (any controlling 0 or A_N==1 forces Y==1)
  always @* if ((A_N===1'b1) || (B===1'b0) || (C===1'b0) || (D===1'b0))
    assert (#0 (Y === 1'b1));

  // Zero case (only one minterm yields Y==0)
  always @* if ((A_N===1'b0) && (B===1'b1) && (C===1'b1) && (D===1'b1))
    assert (#0 (Y === 1'b0));

  // No X on Y when inputs are known
  always @* if (!$isunknown({A_N,B,C,D}))
    assert (#0 (!$isunknown(Y)));

  // X-propagation: if no controlling 0 is present and any input is X/Z, Y must be X
  always @* if (no_ctrl0 && $isunknown({A_N,B,C,D}))
    assert (#0 ($isunknown(Y)));

  // Concise coverage
  always @* begin
    cover (#0 (A_N===1'b1 && Y===1'b1));                               // A_N dominates
    cover (#0 (B===1'b0   && Y===1'b1));                               // B dominates
    cover (#0 (C===1'b0   && Y===1'b1));                               // C dominates
    cover (#0 (D===1'b0   && Y===1'b1));                               // D dominates
    cover (#0 (A_N===1'b0 && B===1'b1 && C===1'b1 && D===1'b1 && Y===1'b0)); // sole 0 case
    cover (#0 (no_ctrl0 && $isunknown({A_N,B,C,D}) && $isunknown(Y))); // X-prop case
    cover (#0 (Y===1'b1));
    cover (#0 (Y===1'b0));
  end
endmodule

bind sky130_fd_sc_ls__nand4b sky130_fd_sc_ls__nand4b_sva u_sva (.Y(Y), .A_N(A_N), .B(B), .C(C), .D(D));