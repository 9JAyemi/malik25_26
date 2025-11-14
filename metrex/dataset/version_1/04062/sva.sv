// SVA checker for ones_counter
// Binds to all instances; focuses on correctness and key coverage
bind ones_counter ones_counter_sva u_ones_counter_sva (.*);

module ones_counter_sva (input [15:0] data_in, input [7:0] ones_out);

  // Immediate assertions on combinational outputs
  always_comb begin
    automatic int n = $countones(data_in);

    // Sanity: no X/Z on IOs
    assert (!$isunknown({data_in, ones_out}))
      else $error("ones_counter: X/Z detected on inputs/outputs");

    // Functional equivalence: popcount
    assert (ones_out == n)
      else $error("ones_counter: ones_out=%0d, expected=%0d (popcount)", ones_out, n);

    // Range/width sanity (redundant with equality but helpful diagnostics)
    assert (ones_out <= 16)
      else $error("ones_counter: ones_out out of range (>16)");
    assert (ones_out[7:5] == 3'b000)
      else $error("ones_counter: high bits of ones_out should be zero");
  end

  // Targeted functional coverage
  always_comb begin
    automatic int n = $countones(data_in);
    cover (n == 0);
    cover (n == 1);
    cover (n == 8);
    cover (n == 15);
    cover (n == 16);          // catches the all-ones edge case
    cover (data_in == 16'h0000);
    cover (data_in == 16'hFFFF);
    cover (data_in == 16'hAAAA);
    cover (data_in == 16'h5555);
  end

endmodule