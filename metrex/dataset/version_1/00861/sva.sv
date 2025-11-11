// SVA for hls_saturation_enqcK — concise, high-quality checks and coverage
// Bind this to the DUT to verify structural wiring and functional behavior.

module hls_saturation_enqcK_sva #(parameter int WIDTH = 28) (
  input  logic [WIDTH-1:0] din0,
  input  logic [WIDTH-1:0] din1,
  input  logic [WIDTH-1:0] din2,
  input  logic [WIDTH-1:0] din3,
  input  logic [1:0]       din4,
  input  logic [WIDTH-1:0] dout,

  // internal taps (for stronger structural checking)
  input  logic [1:0]       sel,
  input  logic [WIDTH-1:0] mux_1_0,
  input  logic [WIDTH-1:0] mux_1_1,
  input  logic [WIDTH-1:0] mux_2_0
);

  // Purely combinational immediate assertions and coverage
  always_comb begin
    // Control must be 2-state (no X/Z on select)
    assert (!$isunknown(din4)) else $error("%m: din4(select) has X/Z");

    // Structural wiring checks (internal nets)
    assert (sel == din4) else $error("%m: sel != din4");
    assert (mux_1_0 == (sel[0] == 1'b0 ? din0 : din1)) else $error("%m: mux_1_0 mismatch");
    assert (mux_1_1 == (sel[0] == 1'b0 ? din2 : din3)) else $error("%m: mux_1_1 mismatch");
    assert (mux_2_0 == (sel[1] == 1'b0 ? mux_1_0 : mux_1_1)) else $error("%m: mux_2_0 mismatch");
    assert (dout == mux_2_0) else $error("%m: dout != mux_2_0");

    // Functional selection checks (only when values are known)
    if (din4 == 2'b00 && !$isunknown(din0)) assert (dout == din0) else $error("%m: sel=00, dout!=din0");
    if (din4 == 2'b01 && !$isunknown(din1)) assert (dout == din1) else $error("%m: sel=01, dout!=din1");
    if (din4 == 2'b10 && !$isunknown(din2)) assert (dout == din2) else $error("%m: sel=10, dout!=din2");
    if (din4 == 2'b11 && !$isunknown(din3)) assert (dout == din3) else $error("%m: sel=11, dout!=din3");

    // Output should not contain X/Z when select and chosen input are known
    if (!$isunknown(din4)) begin
      unique case (din4)
        2'b00: if (!$isunknown(din0)) assert (!$isunknown(dout)) else $error("%m: dout X/Z with sel=00");
        2'b01: if (!$isunknown(din1)) assert (!$isunknown(dout)) else $error("%m: dout X/Z with sel=01");
        2'b10: if (!$isunknown(din2)) assert (!$isunknown(dout)) else $error("%m: dout X/Z with sel=10");
        2'b11: if (!$isunknown(din3)) assert (!$isunknown(dout)) else $error("%m: dout X/Z with sel=11");
      endcase
    end

    // Functional coverage: each select path observed
    cover (din4 == 2'b00 && dout == din0);
    cover (din4 == 2'b01 && dout == din1);
    cover (din4 == 2'b10 && dout == din2);
    cover (din4 == 2'b11 && dout == din3);
  end

endmodule

// Bind into the DUT (connect internal nets for structural checks)
bind hls_saturation_enqcK hls_saturation_enqcK_sva #(.WIDTH(28)) i_hls_saturation_enqcK_sva (
  .din0(din0), .din1(din1), .din2(din2), .din3(din3),
  .din4(din4), .dout(dout),
  .sel(sel), .mux_1_0(mux_1_0), .mux_1_1(mux_1_1), .mux_2_0(mux_2_0)
);