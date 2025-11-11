// SVA for multiplier_block
// Bind-in assertions (no clock needed; uses immediate assertions and covers)

module multiplier_block_sva;
  // Recompute expected intermediates with identical 32-bit ops
  logic [31:0] s_w1, s_w32, s_w31, s_w256, s_w257, s_w2056, s_w2025;

  always_comb begin
    s_w1    = i_data0;
    s_w32   = s_w1   << 5;
    s_w31   = s_w32  - s_w1;
    s_w256  = s_w1   << 8;
    s_w257  = s_w1   + s_w256;
    s_w2056 = s_w257 << 3;
    s_w2025 = s_w2056 - s_w31;

    if (!$isunknown(i_data0)) begin
      // No-X propagation when input is known
      assert (!$isunknown({w1,w32,w31,w256,w257,w2056,w2025,o_data0}))
        else $error("multiplier_block: X/Z on outputs/internal with known input");

      // Stepwise equivalence to spec
      assert (w1    === s_w1)    else $error("w1 mismatch");
      assert (w32   === s_w32)   else $error("w32 mismatch");
      assert (w31   === s_w31)   else $error("w31 mismatch");
      assert (w256  === s_w256)  else $error("w256 mismatch");
      assert (w257  === s_w257)  else $error("w257 mismatch");
      assert (w2056 === s_w2056) else $error("w2056 mismatch");
      assert (w2025 === s_w2025) else $error("w2025 mismatch");
      assert (o_data0 === s_w2025) else $error("o_data0 mismatch");

      // Constant-multiply check: o_data0 == (i_data0 * 2025) mod 2^32
      automatic logic [63:0] prod64 = {32'd0,i_data0} * 64'd2025;
      assert (o_data0 === prod64[31:0])
        else $error("o_data0 != i_data0*2025 (mod 2^32)");
    end

    // Covers (functional scenarios)
    cover (i_data0 == 32'd0 && o_data0 == 32'd0);
    cover (i_data0 == 32'hFFFF_FFFF);
    automatic logic [63:0] p64 = {32'd0,i_data0} * 64'd2025;
    cover (p64[63:32] == 32'd0);   // no overflow in 32b product
    cover (p64[63:32] != 32'd0);   // overflow in 32b product
    cover (i_data0 == 32'd1);
    cover (i_data0 == 32'h8000_0000);
  end
endmodule

// Bind into all instances of multiplier_block
bind multiplier_block multiplier_block_sva sva_multiplier_block();