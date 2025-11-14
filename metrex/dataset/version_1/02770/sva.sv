// Bind these assertions into xlslice
bind xlslice xlslice_sva i_xlslice_sva (
  .Din(Din),
  .Dout(Dout),
  .sliced_signal(sliced_signal),
  .inverted_signal(inverted_signal),
  .shifted_signal(shifted_signal)
);

module xlslice_sva (
  input  logic [23:0] Din,
  input  logic [8:0]  Dout,
  input  logic [15:0] sliced_signal,
  input  logic [15:0] inverted_signal,
  input  logic [8:0]  shifted_signal
);
  // Structural and end-to-end functional checks
  always_comb begin
    assert (sliced_signal   === Din[22:7])             else $error("slice mismatch");
    assert (inverted_signal === ~sliced_signal)         else $error("invert mismatch");
    assert (shifted_signal  === (inverted_signal >> 8)) else $error("shift mismatch");
    assert (Dout            === shifted_signal)         else $error("Dout conn mismatch");

    // End-to-end: Dout = {0, ~Din[22:15]}
    assert (Dout === {1'b0, ~Din[22:15]})               else $error("E2E mapping fail");
    assert (Dout[8] === 1'b0)                           else $error("Dout[8] must be 0");

    // No-X guarantee on known-driving inputs
    if (!$isunknown(Din[22:15])) assert (!$isunknown(Dout)) else $error("Known input produced X/Z on Dout");
  end

  // Bitwise mapping checks + simple coverage
  genvar i;
  generate
    for (i = 0; i < 8; i++) begin : g_bit
      always_comb begin
        assert (Dout[i] === ~Din[i+15]) else $error("Bit map mismatch at Dout[%0d]", i);
        cover (Dout[i] == 1'b0);
        cover (Dout[i] == 1'b1);
      end
    end
  endgenerate

  // Range/extreme coverage
  always_comb begin
    cover (Dout[7:0] == 8'h00);
    cover (Dout[7:0] == 8'hFF);
    cover (Din[22:15] == 8'h00);
    cover (Din[22:15] == 8'hFF);
  end
endmodule