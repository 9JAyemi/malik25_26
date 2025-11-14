// SVA checker for encoder. Bind this to the DUT.
// Focuses on correctness (priority, range, mapping) and practical coverage.
module encoder_sva (
  input logic [39:0] in,
  input logic [5:0]  out
);

  // helper: true if all bits below idx are 0
  function automatic bit lower_zero (input logic [39:0] v, input int idx);
    bit ok = 1'b1;
    for (int j=0; j<idx; j++) ok &= ~v[j];
    return ok;
  endfunction

  // Basic correctness checks
  always_comb begin
    // output domain
    assert (out <= 6'd39) else $error("encoder: out out-of-range %0d", out);

    // all-zero input -> out==0
    if (~|in) assert (out == 6'd0) else $error("encoder: ~|in but out=%0d", out);

    // reverse mapping: out>0 implies in[out]==1 and no lower bits set
    if (out > 6'd0 && out <= 6'd39) begin
      assert (in[out]) else $error("encoder: out=%0d but in[out]==0", out);
      assert (lower_zero(in, out)) else $error("encoder: out=%0d but some lower bit set", out);
    end

    // special-case for out==0: it implies in[0]==1 or all-zero input
    if (out == 6'd0 && !in[0]) assert (~|in) else $error("encoder: out==0 but not in[0] and not all-zero");
  end

  // Forward mapping and coverage for each encoded index
  genvar i;
  generate
    for (i=0; i<40; i++) begin : g_enc
      // forward: if in[i] is the lowest asserted bit, out==i
      always_comb if (in[i] && (i==0 ? 1'b1 : (in[i-1:0] == '0)))
        assert (out == i[5:0]) else $error("encoder: expected out=%0d", i);

      // cover each encoded value being produced
      always @* cover (in[i] && (i==0 ? 1'b1 : (in[i-1:0] == '0)) && out == i[5:0]);
    end
  endgenerate

  // Cover all-zero case
  always @* cover ((in == '0) && out == 6'd0);

  // Cover a multi-bit input exercising priority (higher bits set but lower wins)
  always @* cover (in[0] && (|in[39:1]) && out == 6'd0);
  always @* cover (in[5] && (in[4:0]=='0) && (|in[39:6]) && out == 6'd5);

endmodule

bind encoder encoder_sva enc_sva (.*);