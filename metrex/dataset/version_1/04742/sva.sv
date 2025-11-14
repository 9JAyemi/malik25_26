// SystemVerilog Assertions for multiplier_block
// Bind into the DUT to access internal nets

module multiplier_block_sva();

  // Immediate assertions/coverage suitable for combinational DUTs
  logic [31:0] expected;

  always_comb begin
    expected = i_data0 * 32'd14628;

    if (!$isunknown(i_data0)) begin
      // Structural checks
      assert (w1      == i_data0)            else $error("w1 mismatch");
      assert (w64     == (i_data0 << 6))     else $error("w64 mismatch");
      assert (w63     == (w64 - w1))         else $error("w63 mismatch");
      assert (w504    == (w63 << 3))         else $error("w504 mismatch");
      assert (w4096   == (w1 << 12))         else $error("w4096 mismatch");
      assert (w4097   == (w1 + w4096))       else $error("w4097 mismatch");
      assert (w4161   == (w4097 + w64))      else $error("w4161 mismatch");
      assert (w3657   == (w4161 - w504))     else $error("w3657 mismatch");
      assert (w14628  == (w3657 << 2))       else $error("w14628 mismatch");
      assert (o_data0 == w14628)             else $error("o_data0 path mismatch");

      // Functional equivalence (mod 2^32)
      assert (o_data0 == expected)           else $error("o_data0 != i_data0 * 14628");

      // No-X on output when input known
      assert (!$isunknown(o_data0))          else $error("o_data0 X/Z with known input");
    end

    // Corner-case coverage
    cover (i_data0 == 32'h0000_0000);
    cover (i_data0 == 32'h0000_0001);
    cover (i_data0 == 32'h7FFF_FFFF);
    cover (i_data0 == 32'h8000_0000);
    cover (i_data0 == 32'hFFFF_FFFF);
    cover (o_data0 == 32'h0000_0000);

    // Exercise wrap/borrow and truncation scenarios
    if (!$isunknown(i_data0)) begin
      cover (w4097 < w4096);    // carry on w1 + (i<<12)
      cover (w4161 < w4097);    // carry on + (i<<6)
      cover (w4161 < w504);     // borrow on - (63i<<3)
      cover (|w3657[31:30]);    // MSBs dropped by <<2
    end
  end

endmodule

bind multiplier_block multiplier_block_sva sva_inst();