// SVA for adder: concise, full functional check and key coverage
module adder_sva(input logic [3:0] A, B, input logic [3:0] Z);
  always @* begin
    automatic logic [4:0] sum = A + B;

    // X-prop / sanity
    if (!$isunknown({A,B})) begin
      assert #0 (!$isunknown(Z))
        else $error("adder SVA: Z is X/Z when inputs known A=%0h B=%0h Z=%0h", A, B, Z);
    end

    // Range: result must be 0..9
    assert #0 (Z <= 4'd9)
      else $error("adder SVA: Z out of range (0..9) A=%0d B=%0d Z=%0d sum=%0d", A, B, Z, sum);

    // Golden functionality: mod-10 sum
    assert #0 (Z == (sum % 5'd10))
      else $error("adder SVA: modulo-10 mismatch A=%0d B=%0d Z=%0d sum=%0d", A, B, Z, sum);

    // Explicit branch checks (exercise both code paths)
    if (sum <= 5'd9)
      assert #0 (Z == sum)
        else $error("adder SVA: low-branch mismatch A=%0d B=%0d Z=%0d sum=%0d", A, B, Z, sum);
    else
      assert #0 (Z == (sum - 5'd10))
        else $error("adder SVA: high-branch mismatch A=%0d B=%0d Z=%0d sum=%0d", A, B, Z, sum);

    // Targeted coverage (edges + both branches)
    cover #0 (sum == 5'd0  && Z == 4'd0);   // min
    cover #0 (sum == 5'd9  && Z == 4'd9);   // branch boundary low
    cover #0 (sum == 5'd10 && Z == 4'd0);   // branch boundary high
    cover #0 (sum == 5'd19 && Z == 4'd9);   // upper edge of wrapped range
    cover #0 (sum == 5'd30 && Z == 4'd0);   // absolute max sum
    cover #0 (sum inside {[1:8]});          // low branch interior
    cover #0 (sum inside {[11:18]});        // high branch interior (near boundary)
    cover #0 (sum inside {[20:29]});        // high branch far from boundary
  end
endmodule

// Bind into DUT
bind adder adder_sva adder_sva_i(.A(A), .B(B), .Z(Z));