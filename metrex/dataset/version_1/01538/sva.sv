// SVA checker for multiplier_module
// Bind this module to the DUT.
bind multiplier_module multiplier_module_sva sva_inst();

module multiplier_module_sva;
  // Hierarchical access to i_data0, o_data0, w1..w16

  logic [15:0] model_sum;
  bit in_known;

  always_comb begin
    in_known = !$isunknown(i_data0);

    // Build a 16-bit modular reference model: sum_{k=0..15} (i_data0 << k)
    model_sum = '0;
    if (in_known) begin
      for (int k = 0; k < 16; k++) begin
        model_sum += (i_data0 << k);
      end
    end

    // Sanity
    assert (in_known) else $error("multiplier_module: i_data0 has X/Z");
    if (in_known) assert (!$isunknown(o_data0)) else $error("multiplier_module: o_data0 has X/Z");

    // Functional equivalence (mod 2^16)
    if (in_known) begin
      assert (o_data0 == model_sum) else $error("o_data0 != sum of shifts (ref model)");
      assert (o_data0 == -i_data0) else $error("o_data0 != -i_data0 (mod 2^16)");
      assert ((o_data0 + i_data0)[15:0] == 16'h0000) else $error("o_data0 + i_data0 LSBs not zero");
      assert (o_data0 == (~i_data0 + 16'h0001)) else $error("o_data0 != ~i_data0 + 1 (two's complement)");
    end

    // Structural local checks of shift network
    if (in_known) begin
      assert (w1  == i_data0);
      assert (w2  == (i_data0 << 1));
      assert (w3  == (i_data0 << 2));
      assert (w4  == (i_data0 << 3));
      assert (w5  == (i_data0 << 4));
      assert (w6  == (i_data0 << 5));
      assert (w7  == (i_data0 << 6));
      assert (w8  == (i_data0 << 7));
      assert (w9  == (i_data0 << 8));
      assert (w10 == (i_data0 << 9));
      assert (w11 == (i_data0 << 10));
      assert (w12 == (i_data0 << 11));
      assert (w13 == (i_data0 << 12));
      assert (w14 == (i_data0 << 13));
      assert (w15 == (i_data0 << 14));
      assert (w16 == (i_data0 << 15));
    end

    // Corner cases
    if (in_known && i_data0 == 16'h0000) assert (o_data0 == 16'h0000);
    if (in_known && i_data0 == 16'hFFFF) assert (o_data0 == 16'h0001);
    if (in_known && i_data0 == 16'h8000) assert (o_data0 == 16'h8000);

    // Coverage
    cover (in_known && i_data0 == 16'h0000);
    cover (in_known && i_data0 == 16'h0001);
    cover (in_known && i_data0 == 16'h8000);
    cover (in_known && i_data0 == 16'hFFFF);
    cover (in_known && i_data0 == 16'hAAAA);
    cover (in_known && i_data0 == 16'h5555);
    cover (in_known && o_data0 == 16'h0000);
    cover (in_known && ((o_data0 + i_data0)[15:0] == 16'h0000));
  end
endmodule