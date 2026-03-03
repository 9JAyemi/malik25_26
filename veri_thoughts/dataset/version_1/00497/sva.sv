// SVA checker for abs_difference_sum
// Bind this into the DUT: bind abs_difference_sum abs_difference_sum_sva sva();

module abs_difference_sum_sva (abs_difference_sum dut);

  function automatic [3:0] abs4(input [3:0] a, input [3:0] b);
    abs4 = (a > b) ? (a - b) : (b - a);
  endfunction

  // Functional correctness per nibble and full concatenation
  always_comb begin
    assert (dut.output_sum[3:0]   == abs4(dut.input_a[3:0],   dut.input_b[3:0]))
      else $error("abs_diff[3:0] mismatch: a=%0h b=%0h out=%0h", dut.input_a[3:0], dut.input_b[3:0], dut.output_sum[3:0]);
    assert (dut.output_sum[7:4]   == abs4(dut.input_a[7:4],   dut.input_b[7:4]))
      else $error("abs_diff[7:4] mismatch: a=%0h b=%0h out=%0h", dut.input_a[7:4], dut.input_b[7:4], dut.output_sum[7:4]);
    assert (dut.output_sum[11:8]  == abs4(dut.input_a[11:8],  dut.input_b[11:8]))
      else $error("abs_diff[11:8] mismatch: a=%0h b=%0h out=%0h", dut.input_a[11:8], dut.input_b[11:8], dut.output_sum[11:8]);
    assert (dut.output_sum[15:12] == abs4(dut.input_a[15:12], dut.input_b[15:12]))
      else $error("abs_diff[15:12] mismatch: a=%0h b=%0h out=%0h", dut.input_a[15:12], dut.input_b[15:12], dut.output_sum[15:12]);

    assert (dut.output_sum ==
            { abs4(dut.input_a[15:12], dut.input_b[15:12]),
              abs4(dut.input_a[11:8],  dut.input_b[11:8]),
              abs4(dut.input_a[7:4],   dut.input_b[7:4]),
              abs4(dut.input_a[3:0],   dut.input_b[3:0]) })
      else $error("output_sum concatenation mismatch: a=%0h b=%0h out=%0h",
                  dut.input_a, dut.input_b, dut.output_sum);

    // Word-level identity when inputs equal
    if (dut.input_a == dut.input_b)
      assert (dut.output_sum == 16'h0000)
        else $error("Expected zero when input_a==input_b: a=b=%0h out=%0h", dut.input_a, dut.output_sum);
  end

  // X-propagation safety: known inputs -> known outputs (per nibble)
  always_comb begin
    if (!$isunknown({dut.input_a[3:0],   dut.input_b[3:0]}))   assert (!$isunknown(dut.output_sum[3:0]))   else $error("X/Z leaked to output_sum[3:0]");
    if (!$isunknown({dut.input_a[7:4],   dut.input_b[7:4]}))   assert (!$isunknown(dut.output_sum[7:4]))   else $error("X/Z leaked to output_sum[7:4]");
    if (!$isunknown({dut.input_a[11:8],  dut.input_b[11:8]}))  assert (!$isunknown(dut.output_sum[11:8]))  else $error("X/Z leaked to output_sum[11:8]");
    if (!$isunknown({dut.input_a[15:12], dut.input_b[15:12]})) assert (!$isunknown(dut.output_sum[15:12])) else $error("X/Z leaked to output_sum[15:12]");
  end

  // Functional coverage (immediate cover) – exercise both branches and equality per nibble
  always_comb begin
    cover (dut.input_a[3:0]   >  dut.input_b[3:0]);
    cover (dut.input_a[3:0]   <  dut.input_b[3:0]);
    cover (dut.input_a[3:0]   == dut.input_b[3:0]);

    cover (dut.input_a[7:4]   >  dut.input_b[7:4]);
    cover (dut.input_a[7:4]   <  dut.input_b[7:4]);
    cover (dut.input_a[7:4]   == dut.input_b[7:4]);

    cover (dut.input_a[11:8]  >  dut.input_b[11:8]);
    cover (dut.input_a[11:8]  <  dut.input_b[11:8]);
    cover (dut.input_a[11:8]  == dut.input_b[11:8]);

    cover (dut.input_a[15:12] >  dut.input_b[15:12]);
    cover (dut.input_a[15:12] <  dut.input_b[15:12]);
    cover (dut.input_a[15:12] == dut.input_b[15:12]);

    // Corner patterns
    cover ((dut.input_a == 16'hFFFF) && (dut.input_b == 16'h0000) && (dut.output_sum == 16'hFFFF));
    cover ((dut.input_a == 16'h0000) && (dut.input_b == 16'hFFFF) && (dut.output_sum == 16'hFFFF));
    cover ((dut.input_a == dut.input_b) && (dut.output_sum == 16'h0000));
  end

endmodule