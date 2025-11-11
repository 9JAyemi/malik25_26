// SVA for module: multiplier
// Bind this file to the DUT
bind multiplier multiplier_sva u_multiplier_sva(.*);

module multiplier_sva(
  input  logic [7:0]  A,B,C,D,E,
  input  logic [15:0] Y
);

  // Compute golden result in wide precision to avoid intermediate truncation
  logic [31:0] ab, cde, sum32;
  always_comb begin
    ab    = A * B;          // 16-bit math, stored in 32-bit container
    cde   = (C * D) * E;    // 24-bit math, stored in 32-bit container
    sum32 = ab + cde;       // up to 25 bits, in 32-bit container
  end

  // Core correctness: Y is the low 16 bits (mod 2^16) of the full-precision sum
  always_comb begin
    assert (!$isunknown({A,B,C,D,E,Y})) else $error("X/Z detected on interface");
    assert (Y == sum32[15:0])
      else $error("Y mismatch: got=%0h exp=%0h (A=%0h B=%0h C=%0h D=%0h E=%0h)",
                  Y, sum32[15:0], A,B,C,D,E);
  end

  // Functional corner-case checks (also serve as covers)
  always_comb begin
    // If AB path is zero, Y must equal CDE truncated
    if ((A==0) || (B==0)) begin
      assert (Y == cde[15:0])
        else $error("AB zero, expected Y=cde[15:0]");
      cover (1); // AB-zero scenario observed
    end

    // If CDE path is zero, Y must equal AB truncated
    if ((C==0) || (D==0) || (E==0)) begin
      assert (Y == ab[15:0])
        else $error("CDE zero, expected Y=ab[15:0]");
      cover (1); // CDE-zero scenario observed
    end

    // Both paths zero -> Y must be zero
    if (((A==0)||(B==0)) && ((C==0)||(D==0)||(E==0))) begin
      assert (Y == 16'h0000) else $error("All-zero paths, expected Y=0");
      cover (1); // both-zero scenario observed
    end
  end

  // Overflow/truncation observability
  always_comb begin
    cover (sum32[31:16] == 16'h0000); // no overflow (full sum fits in 16 bits)
    cover (sum32[31:16] != 16'h0000); // overflow occurred (truncation exercised)
  end

  // Extremes and stress covers
  always_comb begin
    cover (Y == 16'h0000);
    cover (Y == 16'hFFFF);
    cover ((A==8'hFF) && (B==8'hFF));                 // max AB
    cover ((C==8'hFF) && (D==8'hFF) && (E==8'hFF));   // max CDE
    cover ((A==8'h01) && (B==8'h01));                 // min non-zero AB
    cover ((C==8'h01) && (D==8'h01) && (E==8'h01));   // min non-zero CDE
  end

endmodule