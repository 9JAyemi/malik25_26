// SVA for mux_2_1
// Bind-in assertion module (concise, checks core functionality and coverage)

module mux_2_1_sva (
  input logic A, B, S, Y,
  input logic VPWR, VGND, VPB, VNB,
  input logic not_S
);

  // Core equivalence and X-propagation checks
  always_comb begin
    // 4-state functional check
    assert (Y === ((A & ~S) | (B & S)))
      else $error("mux_2_1: Y != (A & ~S) | (B & S). A=%b B=%b S=%b Y=%b",A,B,S,Y);

    // Internal inversion check
    assert (not_S === ~S)
      else $error("mux_2_1: not_S != ~S. S=%b not_S=%b", S, not_S);

    // Known-input -> known-output, and 2-state correctness
    if (! $isunknown({A,B,S})) begin
      assert (! $isunknown(Y))
        else $error("mux_2_1: Y is X/Z while inputs known. A=%b B=%b S=%b Y=%b",A,B,S,Y);
      assert (Y == (S ? B : A))
        else $error("mux_2_1: functional mismatch (2-state). A=%0b B=%0b S=%0b Y=%0b",A,B,S,Y);
    end

    // Power pins sanity (should be constant rails)
    assert (VPWR === 1'b1) else $error("mux_2_1: VPWR != 1");
    assert (VPB  === 1'b1) else $error("mux_2_1: VPB  != 1");
    assert (VGND === 1'b0) else $error("mux_2_1: VGND != 0");
    assert (VNB  === 1'b0) else $error("mux_2_1: VNB  != 0");
  end

  // Coverage: all input combinations (no X/Z), both paths and both Y values
  always_comb begin
    cover (! $isunknown({A,B,S}) && {S,B,A}===3'b000);
    cover (! $isunknown({A,B,S}) && {S,B,A}===3'b001);
    cover (! $isunknown({A,B,S}) && {S,B,A}===3'b010);
    cover (! $isunknown({A,B,S}) && {S,B,A}===3'b011);
    cover (! $isunknown({A,B,S}) && {S,B,A}===3'b100);
    cover (! $isunknown({A,B,S}) && {S,B,A}===3'b101);
    cover (! $isunknown({A,B,S}) && {S,B,A}===3'b110);
    cover (! $isunknown({A,B,S}) && {S,B,A}===3'b111);

    cover (! $isunknown({A,B,S,Y}) && (S==0) && (Y==0));
    cover (! $isunknown({A,B,S,Y}) && (S==0) && (Y==1));
    cover (! $isunknown({A,B,S,Y}) && (S==1) && (Y==0));
    cover (! $isunknown({A,B,S,Y}) && (S==1) && (Y==1));

    cover (! $isunknown(not_S) && not_S==0);
    cover (! $isunknown(not_S) && not_S==1);
  end

endmodule

bind mux_2_1 mux_2_1_sva u_mux_2_1_sva (
  .A(A), .B(B), .S(S), .Y(Y),
  .VPWR(VPWR), .VGND(VGND), .VPB(VPB), .VNB(VNB),
  .not_S(not_S)
);