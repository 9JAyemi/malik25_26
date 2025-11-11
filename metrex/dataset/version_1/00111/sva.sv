// SVA checker for barrel_shifter
// Focuses on combinational correctness of internal stages and Y mapping,
// plus concise functional coverage.
//
// Bind this checker to the DUT:
//   bind barrel_shifter barrel_shifter_sva bs_sva();
//
// No clock required; uses immediate assertions in always_comb.

module barrel_shifter_sva;
  // Bound into barrel_shifter; can directly see A, B, Y, stage*_out
  // synthesis translate_off

  // Combinational correctness of internal stages
  always_comb begin
    assert (#0) (stage1_out == (B[0] ? {A[6:0], 1'b0} : {1'b0, A[7:1]}))
      else $error("stage1_out mismatch: B[0]=%0b A=%0h got=%0h", B[0], A, stage1_out);

    assert (#0) (stage2_out == (B[1] ? {stage1_out[5:0], 2'b00} : {2'b00, stage1_out[7:2]}))
      else $error("stage2_out mismatch: B[1]=%0b stage1_out=%0h got=%0h", B[1], stage1_out, stage2_out);

    assert (#0) (stage3_out == (B[2] ? {stage2_out[3:0], 4'b0000} : {4'b0000, stage2_out[7:4]}))
      else $error("stage3_out mismatch: B[2]=%0b stage2_out=%0h got=%0h", B[2], stage2_out, stage3_out);
  end

  // Y must match the RTL case mapping exactly
  always_comb begin
    logic [7:0] expY;
    unique case (B)
      3'b000: expY = A;
      3'b001: expY = stage1_out;                  // 1-bit zero-fill shift via stage1
      3'b010: expY = {A[1:0], A[7:2]};            // rotate-left 2
      3'b011: expY = {A[2:0], A[7:3]};            // rotate-left 3
      3'b111: expY = stage3_out;                  // 4-bit zero-fill shift via stage3
      3'b110: expY = {A[4:0], A[7:5]};            // rotate-left 5
      3'b101: expY = {A[5:0], A[7:6]};            // rotate-left 6
      default: expY = 8'h00;                      // B == 3'b100
    endcase

    assert (#0) (Y === expY)
      else $error("Y mismatch: B=%0b A=%0h exp=%0h got=%0h", B, A, expY, Y);

    // Direct ties when case uses stage results
    assert (#0) (!(B==3'b001) || (Y === stage1_out))
      else $error("Y != stage1_out for B=001: A=%0h Y=%0h stage1=%0h", A, Y, stage1_out);

    assert (#0) (!(B==3'b111) || (Y === stage3_out))
      else $error("Y != stage3_out for B=111: A=%0h Y=%0h stage3=%0h", A, Y, stage3_out);
  end

  // Functional coverage: all B values + key A patterns (concise)
  always_comb begin
    // B space
    cover (B == 3'b000);
    cover (B == 3'b001);
    cover (B == 3'b010);
    cover (B == 3'b011);
    cover (B == 3'b100);
    cover (B == 3'b101);
    cover (B == 3'b110);
    cover (B == 3'b111);

    // Corner A patterns
    cover (A == 8'h00);
    cover (A == 8'hFF);
    cover (A == 8'h01);
    cover (A == 8'h80);
    cover (A == 8'hAA);
    cover (A == 8'h55);

    // A few targeted combos to hit both stage and rotate paths
    cover (A == 8'h01 && B == 3'b001);
    cover (A == 8'h80 && B == 3'b111);
    cover (A == 8'hAA && (B == 3'b010 || B == 3'b011 || B == 3'b101 || B == 3'b110));
    cover (A == 8'h55 && B == 3'b100);
  end

  // synthesis translate_on
endmodule

bind barrel_shifter barrel_shifter_sva bs_sva();