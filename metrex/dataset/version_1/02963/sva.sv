// SVA for feedforward_mux_4to1_sel2_8_1
// Concise, bound checker verifying internal chain and end-to-end behavior, plus coverage.
`ifndef SYNTHESIS
module ffmux4to1_sva_checker (
  input  logic [7:0] din1,
  input  logic [7:0] din2,
  input  logic [7:0] din3,
  input  logic [7:0] din4,
  input  logic [1:0] din5,
  input  logic [7:0] dout,
  input  logic [1:0] sel,
  input  logic [7:0] mux_1_0,
  input  logic [7:0] mux_1_1,
  input  logic [7:0] mux_2_0
);

  // Combinational immediate assertions (portable for clockless DUT)
  always_comb begin
    // Basic sanity
    assert (!$isunknown(din5)) else $error("feedforward_mux_4to1: sel(din5) has X/Z");
    assert (sel === din5)      else $error("feedforward_mux_4to1: sel != din5");

    // Internal tree correctness
    assert (mux_1_0 === ((sel[0]==1'b0) ? din1 : din2)) else $error("feedforward_mux_4to1: mux_1_0 mismatch");
    assert (mux_1_1 === ((sel[0]==1'b0) ? din3 : din4)) else $error("feedforward_mux_4to1: mux_1_1 mismatch");
    assert (mux_2_0 === ((sel[1]==1'b0) ? mux_1_0 : mux_1_1)) else $error("feedforward_mux_4to1: mux_2_0 mismatch");
    assert (dout    === mux_2_0) else $error("feedforward_mux_4to1: dout != mux_2_0");

    // End-to-end 4:1 mapping
    unique case (din5)
      2'b00: assert (dout === din1) else $error("feedforward_mux_4to1: sel=00, dout!=din1");
      2'b01: assert (dout === din2) else $error("feedforward_mux_4to1: sel=01, dout!=din2");
      2'b10: assert (dout === din3) else $error("feedforward_mux_4to1: sel=10, dout!=din3");
      2'b11: assert (dout === din4) else $error("feedforward_mux_4to1: sel=11, dout!=din4");
      default: ; // X/Z already flagged
    endcase

    // No-X propagation on known select + known selected input
    if (!$isunknown(din5)) begin
      if ((din5==2'b00) && !$isunknown(din1)) assert (!$isunknown(dout)) else $error("feedforward_mux_4to1: dout X with sel=00 and known din1");
      if ((din5==2'b01) && !$isunknown(din2)) assert (!$isunknown(dout)) else $error("feedforward_mux_4to1: dout X with sel=01 and known din2");
      if ((din5==2'b10) && !$isunknown(din3)) assert (!$isunknown(dout)) else $error("feedforward_mux_4to1: dout X with sel=10 and known din3");
      if ((din5==2'b11) && !$isunknown(din4)) assert (!$isunknown(dout)) else $error("feedforward_mux_4to1: dout X with sel=11 and known din4");
    end

    // Functional coverage (select encodings and mapping)
    cover (din5 == 2'b00);
    cover (din5 == 2'b01);
    cover (din5 == 2'b10);
    cover (din5 == 2'b11);

    cover (din5==2'b00 && dout==din1);
    cover (din5==2'b01 && dout==din2);
    cover (din5==2'b10 && dout==din3);
    cover (din5==2'b11 && dout==din4);
  end

endmodule

// Bind into the DUT to access internal nets
bind feedforward_mux_4to1_sel2_8_1 ffmux4to1_sva_checker u_ffmux4to1_sva_checker (
  .din1(din1),
  .din2(din2),
  .din3(din3),
  .din4(din4),
  .din5(din5),
  .dout(dout),
  .sel(sel),
  .mux_1_0(mux_1_0),
  .mux_1_1(mux_1_1),
  .mux_2_0(mux_2_0)
);
`endif