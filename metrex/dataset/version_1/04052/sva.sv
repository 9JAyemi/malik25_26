// SVA binder for shift_add_multiplier
module shift_add_multiplier_sva (shift_add_multiplier dut);

  function automatic logic [31:0] sum_of_shifts(input logic [15:0] fa, fb);
    logic [31:0] acc;
    int k;
    begin
      acc = 32'h0;
      for (k = 0; k < 16; k++) begin
        if (fb[k]) acc += ({16'h0, fa} << k);
      end
      return acc;
    end
  endfunction

  // Core functional checks (combinational immediate assertions)
  always_comb begin
    assert (!$isunknown({dut.a, dut.b})) else
      $error("X/Z on inputs: a=%h b=%h", dut.a, dut.b);

    assert (dut.out == sum_of_shifts(dut.a, dut.b)) else
      $error("sum_of_shifts mismatch: a=%h b=%h out=%h exp=%h",
             dut.a, dut.b, dut.out, sum_of_shifts(dut.a, dut.b));

    assert (dut.out == ({16'h0, dut.a} * {16'h0, dut.b})) else
      $error("mul mismatch: a=%h b=%h out=%h exp=%h",
             dut.a, dut.b, dut.out, ({16'h0, dut.a} * {16'h0, dut.b}));

    if ((dut.a == 16'h0) || (dut.b == 16'h0))
      assert (dut.out == 32'h0) else
        $error("zero operand rule failed: a=%h b=%h out=%h", dut.a, dut.b, dut.out);

    if (dut.a == 16'h1)
      assert (dut.out == {16'h0, dut.b}) else
        $error("a==1 rule failed: b=%h out=%h", dut.b, dut.out);

    if (dut.b == 16'h1)
      assert (dut.out == {16'h0, dut.a}) else
        $error("b==1 rule failed: a=%h out=%h", dut.a, dut.out);

    assert (dut.out[0] == (dut.a[0] & dut.b[0])) else
      $error("LSB mismatch: a0=%0b b0=%0b out0=%0b", dut.a[0], dut.b[0], dut.out[0]);

    // Internal sanity (implementation consistency)
    assert (dut.multiplicand == dut.a) else
      $error("internal multiplicand mismatch: multiplicand=%h a=%h", dut.multiplicand, dut.a);

    assert (dut.multiplier == 16'h0) else
      $error("internal multiplier not fully shifted to zero: multiplier=%h", dut.multiplier);

    assert (dut.product == dut.out) else
      $error("internal product/out mismatch: product=%h out=%h", dut.product, dut.out);
  end

  // Lightweight coverage (important corners and patterns)
  always_comb begin
    cover (dut.a == 16'h0000 && dut.b == 16'h0000);
    cover (dut.a == 16'h0001);
    cover (dut.b == 16'h0001);
    cover (dut.a == 16'hFFFF && dut.b == 16'hFFFF);
    cover (dut.a == 16'hAAAA && dut.b == 16'h5555);
    cover ($onehot(dut.a));
    cover ($onehot(dut.b));
    cover ($countones(dut.a) == 8);
    cover ($countones(dut.b) == 8);
  end

  genvar k;
  generate
    for (k = 0; k < 16; k++) begin: onehot_cov
      always_comb begin
        cover (dut.b == (16'h1 << k));
        cover (dut.a == (16'h1 << k));
      end
    end
  endgenerate

endmodule

bind shift_add_multiplier shift_add_multiplier_sva sva_inst();