// SVA checker for addsub
// Binds to the DUT and verifies result, carry/borrow, and signed overflow.
// Includes concise functional coverage on key scenarios.

module addsub_sva #(parameter W=4)
(
  input logic [W-1:0] A,
  input logic [W-1:0] B,
  input logic         M,
  input logic [W-1:0] R,
  input logic         COUT,
  input logic         V
);
  logic [W-1:0] b_eff;
  logic [W:0]   sum;

  always_comb begin
    if (!$isunknown({A,B,M,R,COUT,V})) begin
      b_eff = M ? (~B + 1'b1) : B;              // two's comp B when subtract
      sum   = {1'b0, A} + {1'b0, b_eff};        // 5-bit true arithmetic

      // Core equivalence checks
      assert (R    === sum[W-1:0]) else $error("R mismatch: exp=%0h got=%0h", sum[W-1:0], R);
      assert (COUT === (sum[W] ^ M)) else $error("COUT mismatch: exp=%0b got=%0b", (sum[W]^M), COUT);

      // Correct signed overflow (uses effective operand, not raw B)
      assert (V === ((A[W-1] == b_eff[W-1]) && (sum[W-1] != A[W-1])))
        else $error("V mismatch (signed overflow): A=%0h B=%0h M=%0b R=%0h", A,B,M,R);

      // Mode-specific semantic sanity
      if (!M) begin
        assert (R    === ((A + B) & ((1<<W)-1))) else $error("ADD R bad");
        assert (COUT === ((A + B) >> W))         else $error("ADD COUT bad");
      end else begin
        assert (R    === ((A - B) & ((1<<W)-1))) else $error("SUB R bad");
        assert (COUT === (A < B))                else $error("SUB borrow bad");
      end

      // Immediate coverage of key behaviors
      cover (!M && (sum[W] == 1'b1));  // add carry
      cover (!M && (V == 1'b1));       // add overflow
      cover (!M && (R == '0));         // add zero
      cover ( M && (COUT == 1'b1));    // sub borrow
      cover ( M && (V == 1'b1));       // sub overflow
      cover ( M && (R == '0));         // sub zero
      cover (!M && (A[W-1]==0) && (B[W-1]==0) && (V==1)); // +pos +pos => overflow
      cover ( M && (A[W-1]==1) && (B[W-1]==0) && (V==1)); // neg - pos => overflow
    end
  end
endmodule

// Bind into the DUT
bind addsub addsub_sva #(.W(4)) addsub_sva_i (
  .A(A), .B(B), .M(M), .R(R), .COUT(COUT), .V(V)
);