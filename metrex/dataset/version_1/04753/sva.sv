// SVA for multiplier_block
// Checks structural relations, mathematical equivalence (o = i*8790 mod 2^32),
// X-propagation, and provides concise functional coverage.

module multiplier_block_sva (
  input logic [31:0] i_data0,
  input logic [31:0] o_data0,
  // internal taps
  input logic [31:0] w1,
  input logic [31:0] w32,
  input logic [31:0] w33,
  input logic [31:0] w4096,
  input logic [31:0] w4129,
  input logic [31:0] w2,
  input logic [31:0] w4131,
  input logic [31:0] w264,
  input logic [31:0] w4395,
  input logic [31:0] w8790
);

  // Combinational, clockless immediate assertions
  always_comb begin
    // Knownness/X checks when input is known
    if (!$isunknown(i_data0)) begin
      assert (!$isunknown({o_data0,w1,w2,w32,w33,w4096,w4129,w4131,w264,w4395,w8790}))
        else $error("multiplier_block: X/Z detected on internal/output with known input");
    end

    // Structural relations
    assert (w1    == i_data0)           else $error("w1 mismatch");
    assert (w2    == (w1 << 1))         else $error("w2 mismatch");
    assert (w32   == (w1 << 5))         else $error("w32 mismatch");
    assert (w33   == (w1 + w32))        else $error("w33 mismatch");
    assert (w4096 == (w1 << 12))        else $error("w4096 mismatch");
    assert (w4129 == (w33 + w4096))     else $error("w4129 mismatch");
    assert (w4131 == (w4129 + w2))      else $error("w4131 mismatch");
    assert (w264  == (w33 << 3))        else $error("w264 mismatch");
    assert (w4395 == (w4131 + w264))    else $error("w4395 mismatch");
    assert (w8790 == (w4395 << 1))      else $error("w8790 mismatch");
    assert (o_data0 == w8790)           else $error("o_data0 mismatch (vs w8790)");

    // Mathematical equivalence (mod 2^32) for key nodes
    assert (w33   == (i_data0 * 32'd33  )[31:0])   else $error("w33 != i*33 (mod 2^32)");
    assert (w264  == (i_data0 * 32'd264 )[31:0])   else $error("w264 != i*264 (mod 2^32)");
    assert (w4129 == (i_data0 * 32'd4129)[31:0])   else $error("w4129 != i*4129 (mod 2^32)");
    assert (w4131 == (i_data0 * 32'd4131)[31:0])   else $error("w4131 != i*4131 (mod 2^32)");
    assert (w4395 == (i_data0 * 32'd4395)[31:0])   else $error("w4395 != i*4395 (mod 2^32)");
    assert (w8790 == (i_data0 * 32'd8790)[31:0])   else $error("w8790 != i*8790 (mod 2^32)");
    assert (o_data0 == (i_data0 * 32'd8790)[31:0]) else $error("o != i*8790 (mod 2^32)");

    // Minimal functional coverage
    cover (i_data0 == 32'h0000_0000);
    cover (i_data0 == 32'h0000_0001);
    cover (i_data0 == 32'hFFFF_FFFF);
    cover (i_data0[31]);               // MSB set
    cover (|i_data0[31:27]);           // bits dropped by <<5 path
    cover (|i_data0[31:20]);           // bits dropped by <<12 path
    cover (|i_data0[31:29]);           // bits dropped by <<3 path
    cover (o_data0 == 32'h0000_0000);  // wrap-to-zero case
  end

endmodule

// Bind into the DUT to access internal nets
bind multiplier_block multiplier_block_sva m_mult_block_sva (
  .i_data0(i_data0),
  .o_data0(o_data0),
  .w1(w1),
  .w32(w32),
  .w33(w33),
  .w4096(w4096),
  .w4129(w4129),
  .w2(w2),
  .w4131(w4131),
  .w264(w264),
  .w4395(w4395),
  .w8790(w8790)
);