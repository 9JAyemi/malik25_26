// SVA for sky130_fd_sc_ls__clkdlyinv3sd3
// Bind these checks to the DUT; focuses on functional equivalence, rail gating, X-prop, and concise coverage.

module sky130_fd_sc_ls__clkdlyinv3sd3_chk
(
  input  logic A, VPWR, VGND, VPB, VNB,
  input  logic Y,
  input  logic inv1_out, inv2_out, inv3_out, inv4_out
);

  // Functional/structural correctness and safety
  always_comb begin
    // Internal wiring correctness
    assert (inv1_out === ~VGND);
    assert (inv2_out === ~VNB);
    assert (inv3_out === ~VPB);
    assert (inv4_out === ~VPWR);

    // Output functional equivalence
    assert (Y === (A & inv1_out & inv2_out & inv3_out & inv4_out));

    // Necessary conditions when Y is 1
    if (Y === 1'b1) assert (A===1'b1 && VPWR===1'b0 && VPB===1'b0 && VNB===1'b0 && VGND===1'b0);

    // Sufficient rails/inputs forcing Y low
    if (A    === 1'b0) assert (Y === 1'b0);
    if (VPWR === 1'b1) assert (Y === 1'b0);
    if (VPB  === 1'b1) assert (Y === 1'b0);
    if (VNB  === 1'b1) assert (Y === 1'b0);
    if (VGND === 1'b1) assert (Y === 1'b0);

    // No X on Y when all inputs are known
    if (!$isunknown({A,VPWR,VGND,VPB,VNB})) assert (!$isunknown(Y));
  end

  // Compact functional coverage
  always_comb begin
    cover (Y === 1'b1);
    cover (Y === 1'b0);
    // Corner: only way to get Y=1 per RTL
    cover (A && !VPWR && !VPB && !VNB && !VGND && Y);
    // Each rail high should gate Y low
    cover (VPWR && !Y);
    cover (VPB  && !Y);
    cover (VNB  && !Y);
    cover (VGND && !Y);
    // Observe a typical "power-good" rail combo
    cover (VPWR && !VGND && VPB && !VNB);
  end

  // Toggle coverage for all inputs
  always @(posedge A or negedge A)      begin cover ($rose(A));   cover ($fell(A));   end
  always @(posedge VPWR or negedge VPWR)begin cover ($rose(VPWR));cover ($fell(VPWR));end
  always @(posedge VGND or negedge VGND)begin cover ($rose(VGND));cover ($fell(VGND));end
  always @(posedge VPB or negedge VPB)  begin cover ($rose(VPB)); cover ($fell(VPB)); end
  always @(posedge VNB or negedge VNB)  begin cover ($rose(VNB)); cover ($fell(VNB)); end

endmodule

bind sky130_fd_sc_ls__clkdlyinv3sd3 sky130_fd_sc_ls__clkdlyinv3sd3_chk
(
  .A(A), .VPWR(VPWR), .VGND(VGND), .VPB(VPB), .VNB(VNB),
  .Y(Y),
  .inv1_out(inv1_out), .inv2_out(inv2_out), .inv3_out(inv3_out), .inv4_out(inv4_out)
);