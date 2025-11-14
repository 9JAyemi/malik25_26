// SVA checker for comparator. Bind this to the DUT.
// Focused, concise, full functional checks plus branch coverage.

module comparator_sva (comparator dut);

  // Disallow X/Z on inputs (environment constraint)
  assume property (@(dut.A or dut.B or dut.C) !$isunknown({dut.A,dut.B,dut.C}));

  // Internal gate correctness (combinational, race-safe with #0)
  always_comb begin
    assert #0 (dut.Y1_0 === (dut.A[2] & dut.A[1] & dut.C[0]))
      else $error("Y1_0 mismatch");
    assert #0 (dut.Y2_0 === (dut.B[2] & dut.B[1] & dut.C[1]))
      else $error("Y2_0 mismatch");
    assert #0 (dut.Y1_1 === (dut.C[2] & dut.B[0] & dut.Y1_0))
      else $error("Y1_1 mismatch");
    assert #0 (dut.Y2_1 === (dut.A[0] & dut.Y2_0 & dut.Y1_0))
      else $error("Y2_1 mismatch");
  end

  // Output must be known for known inputs
  always_comb assert #0 (!$isunknown(dut.Y))
    else $error("Y is X/Z");

  // Y functional mapping check
  logic [1:0] exp;
  always_comb begin
    unique case (1'b1)
      (dut.Y1_0 & dut.Y2_0 & ~dut.Y1_1 & ~dut.Y2_1): exp = 2'b00;
      (dut.Y1_0 & dut.Y2_0 & ~dut.Y1_1 &  dut.Y2_1): exp = 2'b01;
      (dut.Y1_0 & dut.Y2_0 &  dut.Y1_1 & ~dut.Y2_1): exp = 2'b10;
      default:                                       exp = 2'b11;
    endcase
    assert #0 (dut.Y == exp)
      else $error("Y mismatch exp=%b got=%b", exp, dut.Y);
  end

  // Branch and result coverage
  cover property (@(dut.A or dut.B or dut.C) dut.Y1_0 & dut.Y2_0 & ~dut.Y1_1 & ~dut.Y2_1 && dut.Y==2'b00);
  cover property (@(dut.A or dut.B or dut.C) dut.Y1_0 & dut.Y2_0 & ~dut.Y1_1 &  dut.Y2_1 && dut.Y==2'b01);
  cover property (@(dut.A or dut.B or dut.C) dut.Y1_0 & dut.Y2_0 &  dut.Y1_1 & ~dut.Y2_1 && dut.Y==2'b10);
  cover property (@(dut.A or dut.B or dut.C) ~(dut.Y1_0 & dut.Y2_0)                         && dut.Y==2'b11);
  cover property (@(dut.A or dut.B or dut.C)  dut.Y1_0 & dut.Y2_0 &  dut.Y1_1 & dut.Y2_1    && dut.Y==2'b11);

endmodule

bind comparator comparator_sva u_comparator_sva(.dut());