// SVA for binary_ones_counter
// Bind this checker to the DUT instance
// bind binary_ones_counter binary_ones_counter_sva sva(.data_in(data_in), .ones_count(ones_count));

module binary_ones_counter_sva (
  input  logic [15:0] data_in,
  input  logic [3:0]  ones_count
);

  // Functional correctness (modulo-16 of true popcount)
  a_popcount_trunc: assert property (@(data_in)
    ones_count == $countones(data_in)[3:0]
  ) else $error("ones_count != popcount(data_in) modulo 16");

  // Exact correctness when no overflow (0..15)
  a_popcount_exact: assert property (@(data_in)
    ($countones(data_in) <= 15) |-> (ones_count == $countones(data_in)[3:0])
  ) else $error("ones_count should equal exact popcount when <=15");

  // Explicitly flag overflow case (true count = 16 can’t be represented in 4 bits)
  a_overflow_flag: assert property (@(data_in)
    $countones(data_in) != 16
  ) else $error("Overflow: popcount=16 cannot be represented in 4-bit ones_count");

  // Known-propagation: known input implies known output
  a_no_x: assert property (@(data_in)
    (!$isunknown(data_in)) |-> (!$isunknown(ones_count))
  ) else $error("ones_count has X/Z while data_in is known");

  // No spurious output changes without input change (combinational behavior)
  a_no_spurious_change: assert property (@(ones_count)
    $changed(ones_count) |-> $changed(data_in)
  ) else $error("ones_count changed without data_in change");

  // Minimal functional coverage
  cover_zero:      cover property (@(data_in) (data_in == 16'h0000) && (ones_count == 4'd0));
  cover_mid:       cover property (@(data_in) ($countones(data_in) == 8)  && (ones_count == 4'd8));
  cover_15:        cover property (@(data_in) ($countones(data_in) == 15) && (ones_count == 4'd15));
  cover_overflow:  cover property (@(data_in) (data_in == 16'hFFFF) && (ones_count == 4'd0));

endmodule