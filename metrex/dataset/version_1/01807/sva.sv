// SVA for sky130_fd_sc_hdll__or4b: X = A | B | C | ~D_N
// Bind this checker to the DUT.

module sky130_fd_sc_hdll__or4b_sva (
  input logic X,
  input logic A,
  input logic B,
  input logic C,
  input logic D_N
);

  // Functional equivalence (delta-cycle) when inputs are resolved
  always_comb begin
    if (!$isunknown({A,B,C,D_N})) begin
      assert #0 (X === (A | B | C | ~D_N))
        else $error("or4b func mismatch: X=%0b exp=%0b A=%0b B=%0b C=%0b D_N=%0b",
                    X, (A|B|C|~D_N), A,B,C,D_N);
      assert #0 (!$isunknown(X))
        else $error("or4b: resolved inputs produced X/Z on X");
    end
  end

  // Forcing conditions that must hold even with unknowns on other pins
  always_comb begin
    if (D_N === 1'b0)  assert #0 (X === 1'b1) else $error("or4b: D_N=0 must force X=1");
    if (A   === 1'b1)  assert #0 (X === 1'b1) else $error("or4b: A=1 must force X=1");
    if (B   === 1'b1)  assert #0 (X === 1'b1) else $error("or4b: B=1 must force X=1");
    if (C   === 1'b1)  assert #0 (X === 1'b1) else $error("or4b: C=1 must force X=1");
    if (A===1'b0 && B===1'b0 && C===1'b0 && D_N===1'b1)
                       assert #0 (X === 1'b0) else $error("or4b: all-zero inputs must force X=0");
  end

  // Compact functional coverage (key corner cases)
  always_comb begin
    cover (A==0 && B==0 && C==0 && D_N==1 && X==0); // all off -> X=0
    cover (A==1 && B==0 && C==0 && D_N==1 && X==1); // A drives X
    cover (A==0 && B==1 && C==0 && D_N==1 && X==1); // B drives X
    cover (A==0 && B==0 && C==1 && D_N==1 && X==1); // C drives X
    cover (A==0 && B==0 && C==0 && D_N==0 && X==1); // ~D drives X
  end

endmodule

// Bind into the DUT
bind sky130_fd_sc_hdll__or4b sky130_fd_sc_hdll__or4b_sva sva_i (
  .X(X), .A(A), .B(B), .C(C), .D_N(D_N)
);