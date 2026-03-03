// SVA checker for decoder_4to16
// Bind this to the DUT to assert functionality and provide compact coverage.

module decoder_4to16_sva (
  input logic [3:0]  in,
  input logic        ena,
  input logic [15:0] out
);

  // Combinational checks
  always_comb begin
    // No X/Z on inputs/outputs
    assert (!$isunknown({ena,in})) else
      $error("decoder_4to16: X/Z on inputs: ena=%b in=%b", ena, in);
    assert (!$isunknown(out)) else
      $error("decoder_4to16: X/Z on out: out=%h (ena=%b in=%0d)", out, ena, in);

    // At most one zero in out (covers both ena=0 and ena=1 cases)
    assert ($onehot0(~out)) else
      $error("decoder_4to16: >1 zeros in out: out=%h (ena=%b in=%0d)", out, ena, in);

    if (!ena) begin
      // Disabled => all 1s
      assert (out === 16'hFFFF) else
        $error("decoder_4to16: disabled mismatch: out=%h != FFFF", out);
    end else begin
      // Enabled => inverted one-hot with index=in
      assert (out === (16'hFFFF ^ (16'h1 << in))) else
        $error("decoder_4to16: decode mismatch: in=%0d out=%h exp=%h",
               in, out, 16'hFFFF ^ (16'h1 << in));
      // Exactly one zero when enabled
      assert ($onehot(~out)) else
        $error("decoder_4to16: not exactly one zero when enabled: out=%h", out);
    end
  end

  // Per-bit bi-implication (concise and strong)
  genvar gi;
  generate
    for (gi = 0; gi < 16; gi++) begin : g_bit_eq
      always_comb begin
        if (!out[gi]) assert (ena && (in == gi)) else
          $error("decoder_4to16: out[%0d]==0 but ena/in mismatch (ena=%b in=%0d)", gi, ena, in);
        if (ena && (in == gi)) assert (!out[gi]) else
          $error("decoder_4to16: ena=1 in=%0d but out[%0d]!=0 (out=%h)", gi, gi, out);
      end
    end
  endgenerate

  // Compact functional coverage
  // - Each input value hit while enabled and correctly decoded
  // - Disabled output observed
  generate
    for (genvar ci = 0; ci < 16; ci++) begin : g_cov
      always_comb cover (ena && (in == ci) && $onehot(~out) && (out[ci] == 1'b0));
    end
  endgenerate
  always_comb cover (!ena && (out == 16'hFFFF));

endmodule

// Bind to DUT (tools that support bind)
bind decoder_4to16 decoder_4to16_sva sva (.in(in), .ena(ena), .out(out));