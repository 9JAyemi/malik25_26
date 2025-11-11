// SVA checker for bit_counter
// - Uses deferred immediate assertions (assert final) to safely check combinational behavior
// - Default checks true bit-count; set CHECK_PARITY=1 if the intent is parity

module bit_counter_sva #(parameter bit CHECK_PARITY = 1'b0)
(
  input  logic [3:0] in,
  input  logic       count
);

  always @* begin
    // Sanity: no X/Z on inputs/outputs
    assert final (!$isunknown(in))    else $error("bit_counter: X/Z on input in=%b", in);
    assert final (!$isunknown(count)) else $error("bit_counter: X/Z on output count=%b", count);

    // Functional check
    if (!CHECK_PARITY) begin
      // Expect full popcount (0..4); DUT count is 1-bit, so this will expose the truncation bug
      assert final (3'(count) == $countones(in))
        else $error("bit_counter: count(1b=%0b) != popcount(%0d) for in=%b", count, $countones(in), in);
    end else begin
      // If intent is parity
      assert final (count === ^in)
        else $error("bit_counter: parity mismatch count=%0b, ^in=%0b (in=%b)", count, ^in, in);
    end

    // Functional coverage over all popcount classes
    cover ($countones(in) == 0);
    cover ($countones(in) == 1);
    cover ($countones(in) == 2);
    cover ($countones(in) == 3);
    cover ($countones(in) == 4);
  end

endmodule

// Bind to DUT
bind bit_counter bit_counter_sva u_bit_counter_sva (.in(in), .count(count));