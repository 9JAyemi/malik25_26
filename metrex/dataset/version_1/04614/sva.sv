// SVA checker for reverse_bits. Bind this to the DUT.
module reverse_bits_sva(
  input  logic [3:0] B,
  input  logic [3:0] R,
  input  logic [1:0] LZ,
  input  logic [3:0] stage1, stage2, stage3,
  input  logic [1:0] zeros
);
  function automatic logic [3:0] bitrev4(input logic [3:0] x);
    return {x[0],x[1],x[2],x[3]};
  endfunction

  function automatic logic [1:0] lz4_sat3(input logic [3:0] x);
    if (x[3])       return 2'd0;
    else if (x[2])  return 2'd1;
    else if (x[1])  return 2'd2;
    else            return 2'd3; // 000x -> 3 (saturates at 3)
  endfunction

  always_comb begin
    // Top-level functional intent
    if (!$isunknown(B)) begin
      assert (R == bitrev4(B))
        else $error("reverse_bits: R != reverse(B). B=%b R=%b exp=%b", B, R, bitrev4(B));
      assert (LZ == lz4_sat3(R))
        else $error("reverse_bits: LZ wrong for R. R=%b LZ=%0d exp=%0d", R, LZ, lz4_sat3(R));
    end

    // Internal pipeline consistency
    assert (stage1 == bitrev4(B))
      else $error("stage1 wrong. B=%b stage1=%b", B, stage1);
    assert (stage2 == {stage1[1],stage1[0],stage1[3],stage1[2]})
      else $error("stage2 wrong. stage1=%b stage2=%b", stage1, stage2);
    assert (stage3 == {stage2[2],stage2[3],stage2[0],stage2[1]})
      else $error("stage3 wrong. stage2=%b stage3=%b", stage2, stage3);
    assert (R == stage3)
      else $error("R != stage3. R=%b stage3=%b", R, stage3);
    assert (LZ == zeros)
      else $error("LZ != zeros reg. LZ=%0d zeros=%0d", LZ, zeros);

    // Cleanliness
    if (!$isunknown(B))
      assert (!$isunknown({R,LZ,stage1,stage2,stage3,zeros}))
        else $error("Unknowns on outputs/stages with known B. B=%b", B);

    // Coverage (key functional classes)
    cover (R == bitrev4(B));
    cover (LZ == 2'd0 && R[3]            );
    cover (LZ == 2'd1 && R[3:2] == 2'b01 );
    cover (LZ == 2'd2 && R[3:1] == 3'b001);
    cover (LZ == 2'd3 && R        == 4'b0000);
  end
endmodule

bind reverse_bits reverse_bits_sva u_reverse_bits_sva (.*);