// SVA for cmac_padding
// Bind into the DUT to check internal regs as well.

module cmac_padding_sva (
  input  logic [6:0]    length,
  input  logic [127:0]  block_in,
  input  logic [127:0]  block_out,
  input  logic [127:0]  mask,
  input  logic [127:0]  masked_data,
  input  logic [127:0]  padded_data
);
  localparam int W = 128;

  function automatic [W-1:0] exp_mask (input logic [6:0] L);
    int sh;
    sh = W - L;
    // Top-justify L ones: [W-1 : W-L] = 1, rest 0.
    exp_mask = (L == 0) ? '0 : ({W{1'b1}} << sh);
  endfunction

  function automatic int pad_idx (input logic [6:0] L);
    pad_idx = (W-1) - L;
  endfunction

  // Core functional checks (combinational immediate assertions)
  always_comb begin
    // Legal range
    assert (length <= 7'd127)
      else $error("cmac_padding: length out of range (%0d)", length);

    // Mask is exactly top L ones
    assert (mask === exp_mask(length))
      else $error("cmac_padding: mask mismatch");

    // Masking correctness
    assert (masked_data === (block_in & mask))
      else $error("cmac_padding: masked_data mismatch");

    // Padding bit location and value
    assert (padded_data === (masked_data | (128'd1 << pad_idx(length))))
      else $error("cmac_padding: padded_data mismatch");

    // Output equals padded_data
    assert (block_out === padded_data)
      else $error("cmac_padding: block_out mismatch");

    // Below pad bit must be zero (when there are bits below)
    if (length < 7'd127)
      assert (padded_data[pad_idx(length)-1:0] == '0)
        else $error("cmac_padding: bits below pad not zero");

    // Above pad bit must match masked_data (when there are bits above)
    if (length > 7'd0)
      assert (padded_data[W-1:pad_idx(length)+1] == masked_data[W-1:pad_idx(length)+1])
        else $error("cmac_padding: upper bits altered by padding");

    // If inputs known, no X/Z propagate to outputs/internals
    if (!$isunknown({length, block_in})) begin
      assert (!$isunknown(mask))        else $error("cmac_padding: X/Z in mask");
      assert (!$isunknown(masked_data)) else $error("cmac_padding: X/Z in masked_data");
      assert (!$isunknown(padded_data)) else $error("cmac_padding: X/Z in padded_data");
      assert (!$isunknown(block_out))   else $error("cmac_padding: X/Z in block_out");
      // Pad bit must be 1 and was 0 before padding
      assert (padded_data[pad_idx(length)] == 1'b1)
        else $error("cmac_padding: pad bit not set");
      assert (masked_data[pad_idx(length)] == 1'b0)
        else $error("cmac_padding: pad bit not zero before padding");
    end
  end

  // Lightweight functional coverage of key boundary lengths and behaviors
  always_comb begin
    cover (length == 7'd0);
    cover (length == 7'd1);
    cover (length == 7'd7);
    cover (length == 7'd8);
    cover (length == 7'd15);
    cover (length == 7'd16);
    cover (length == 7'd31);
    cover (length == 7'd32);
    cover (length == 7'd63);
    cover (length == 7'd64);
    cover (length == 7'd65);
    cover (length == 7'd126);
    cover (length == 7'd127);

    // Output patterns at extremes
    cover (length == 7'd0   && block_out == (128'd1 << 127));
    cover (length == 7'd127 && block_out[0] && (block_out[127:1] == masked_data[127:1]));
  end
endmodule

bind cmac_padding cmac_padding_sva u_cmac_padding_sva (.*);