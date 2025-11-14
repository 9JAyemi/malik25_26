// SVA checker for adder16 (bindable, no reliance on internals)
module adder16_sva (
  input logic [15:0] A, B,
  input logic        C_in,
  input logic [15:0] S,
  input logic        C_out
);

  // Outputs must match exact mathematical sum
  always_comb begin
    logic [16:0] ref;
    ref = {1'b0, A} + {1'b0, B} + C_in;
    assert ({C_out, S} == ref)
      else $error("adder16 mismatch: A=%0h B=%0h C_in=%0b -> {C_out,S}=%0h exp=%0h",
                  A, B, C_in, {C_out,S}, ref);
  end

  // No X/Z on outputs when inputs are known
  always_comb begin
    if (!$isunknown({A,B,C_in})) begin
      assert (!$isunknown({S,C_out}))
        else $error("adder16 X/Z on outputs for known inputs");
    end
  end

  // Basic identities/corners
  always_comb begin
    assert (!(B==16'h0000 && C_in==1'b0) || (S==A && C_out==1'b0)); // +0
    assert (!(A==16'h0000 && C_in==1'b0) || (S==B && C_out==1'b0)); // +0
    assert (!(A==16'hFFFF && B==16'h0000 && C_in==1'b0) || (S==16'hFFFF && C_out==1'b0));
    assert (!(A==16'hFFFF && B==16'h0000 && C_in==1'b1) || (S==16'h0000 && C_out==1'b1));
    assert (!(A==16'hFFFF && B==16'hFFFF && C_in==1'b1) || (S==16'hFFFF && C_out==1'b1));
  end

  // Lightweight functional coverage (exercise key cases)
  always_comb begin
    // Carry in/out combinations
    cover (C_in==0 && C_out==0);
    cover (C_in==0 && C_out==1);
    cover (C_in==1 && C_out==0);
    cover (C_in==1 && C_out==1);

    // Corners and identities
    cover (A==16'h0000 && B==16'h0000 && C_in==0);           // zero
    cover (B==16'h0000 && C_in==0 && S==A && C_out==0);      // identity
    cover (A==16'hFFFF && B==16'h0000 && C_in==1);           // single overflow
    cover (A==16'hFFFF && B==16'hFFFF && C_in==1);           // full overflow
    cover ({C_out,S}==17'h1_0000);                           // exact 2^16
    cover (S==16'h0000 && C_out==1'b0);                      // zero without carry
    cover (S==16'h0000 && C_out==1'b1);                      // zero with carry (wrap)
  end

endmodule

bind adder16 adder16_sva (.A(A), .B(B), .C_in(C_in), .S(S), .C_out(C_out));