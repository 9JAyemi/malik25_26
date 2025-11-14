// SVA for mux_16to1_sel4_7_1
// Bind this module to the DUT and connect a sampling clk/rst_n.
module mux_16to1_sel4_7_1_sva #(
  parameter int ID = 0,
  parameter int NUM_STAGE = 1,
  parameter int din1_WIDTH  = 7,
  parameter int din2_WIDTH  = 7,
  parameter int din3_WIDTH  = 7,
  parameter int din4_WIDTH  = 7,
  parameter int din5_WIDTH  = 7,
  parameter int din6_WIDTH  = 7,
  parameter int din7_WIDTH  = 7,
  parameter int din8_WIDTH  = 7,
  parameter int din9_WIDTH  = 7,
  parameter int din10_WIDTH = 7,
  parameter int din11_WIDTH = 7,
  parameter int din12_WIDTH = 7,
  parameter int din13_WIDTH = 7,
  parameter int din14_WIDTH = 7,
  parameter int din15_WIDTH = 7,
  parameter int din16_WIDTH = 7,
  parameter int din17_WIDTH = 4,
  parameter int dout_WIDTH  = 7
)(
  input logic clk,
  input logic rst_n,

  input logic [din1_WIDTH-1:0]  din1,
  input logic [din2_WIDTH-1:0]  din2,
  input logic [din3_WIDTH-1:0]  din3,
  input logic [din4_WIDTH-1:0]  din4,
  input logic [din5_WIDTH-1:0]  din5,
  input logic [din6_WIDTH-1:0]  din6,
  input logic [din7_WIDTH-1:0]  din7,
  input logic [din8_WIDTH-1:0]  din8,
  input logic [din9_WIDTH-1:0]  din9,
  input logic [din10_WIDTH-1:0] din10,
  input logic [din11_WIDTH-1:0] din11,
  input logic [din12_WIDTH-1:0] din12,
  input logic [din13_WIDTH-1:0] din13,
  input logic [din14_WIDTH-1:0] din14,
  input logic [din15_WIDTH-1:0] din15,
  input logic [din16_WIDTH-1:0] din16,
  input logic [din17_WIDTH-1:0] din17,

  input logic [3:0] sel,
  input logic [dout_WIDTH-1:0] dout
);

  default clocking cb @ (posedge clk); endclocking
  default disable iff (!rst_n)

  // Canonical mux function (reference model)
  function automatic logic [dout_WIDTH-1:0] f_mux16(
      input logic [3:0] s,
      input logic [dout_WIDTH-1:0] i1,  input logic [dout_WIDTH-1:0] i2,
      input logic [dout_WIDTH-1:0] i3,  input logic [dout_WIDTH-1:0] i4,
      input logic [dout_WIDTH-1:0] i5,  input logic [dout_WIDTH-1:0] i6,
      input logic [dout_WIDTH-1:0] i7,  input logic [dout_WIDTH-1:0] i8,
      input logic [dout_WIDTH-1:0] i9,  input logic [dout_WIDTH-1:0] i10,
      input logic [dout_WIDTH-1:0] i11, input logic [dout_WIDTH-1:0] i12,
      input logic [dout_WIDTH-1:0] i13, input logic [dout_WIDTH-1:0] i14,
      input logic [dout_WIDTH-1:0] i15, input logic [dout_WIDTH-1:0] i16
  );
    unique case (s)
      4'd0:  f_mux16 = i1;
      4'd1:  f_mux16 = i2;
      4'd2:  f_mux16 = i3;
      4'd3:  f_mux16 = i4;
      4'd4:  f_mux16 = i5;
      4'd5:  f_mux16 = i6;
      4'd6:  f_mux16 = i7;
      4'd7:  f_mux16 = i8;
      4'd8:  f_mux16 = i9;
      4'd9:  f_mux16 = i10;
      4'd10: f_mux16 = i11;
      4'd11: f_mux16 = i12;
      4'd12: f_mux16 = i13;
      4'd13: f_mux16 = i14;
      4'd14: f_mux16 = i15;
      4'd15: f_mux16 = i16;
      default: f_mux16 = 'x;
    endcase
  endfunction

  // Knownness guard for functional checks (ignore unused din17)
  wire inputs_known = !$isunknown({
    sel,
    din1, din2, din3, din4,
    din5, din6, din7, din8,
    din9, din10, din11, din12,
    din13, din14, din15, din16
  });

  // Functional equivalence (when inputs are known)
  ap_func: assert property (
    inputs_known |-> (dout == f_mux16(sel,
      din1, din2, din3, din4, din5, din6, din7, din8,
      din9, din10, din11, din12, din13, din14, din15, din16))
  );

  // Output must be known if all relevant controls/data are known
  ap_known: assert property (
    inputs_known |-> !$isunknown(dout)
  );

  // Unused din17 must not affect dout
  ap_din17_no_effect: assert property (
    $changed(din17) && $stable({
      sel,
      din1, din2, din3, din4,
      din5, din6, din7, din8,
      din9, din10, din11, din12,
      din13, din14, din15, din16
    }) |-> $stable(dout)
  );

  // Combinational hold: if select and all used inputs are stable, dout is stable
  ap_hold: assert property (
    $stable({
      sel,
      din1, din2, din3, din4,
      din5, din6, din7, din8,
      din9, din10, din11, din12,
      din13, din14, din15, din16
    }) |-> $stable(dout)
  );

  // Coverage: hit each select value and see matching output
  genvar gi;
  generate
    for (gi = 0; gi < 16; gi++) begin : g_sel_cov
      cover property (
        inputs_known && (sel == gi[3:0]) &&
        (dout == f_mux16(gi[3:0],
          din1, din2, din3, din4, din5, din6, din7, din8,
          din9, din10, din11, din12, din13, din14, din15, din16))
      );
    end
  endgenerate

endmodule

// Example bind (edit clk/rst_n to your TB signals):
// bind mux_16to1_sel4_7_1 mux_16to1_sel4_7_1_sva #(
//   .ID(ID), .NUM_STAGE(NUM_STAGE),
//   .din1_WIDTH(din1_WIDTH), .din2_WIDTH(din2_WIDTH), .din3_WIDTH(din3_WIDTH), .din4_WIDTH(din4_WIDTH),
//   .din5_WIDTH(din5_WIDTH), .din6_WIDTH(din6_WIDTH), .din7_WIDTH(din7_WIDTH), .din8_WIDTH(din8_WIDTH),
//   .din9_WIDTH(din9_WIDTH), .din10_WIDTH(din10_WIDTH), .din11_WIDTH(din11_WIDTH), .din12_WIDTH(din12_WIDTH),
//   .din13_WIDTH(din13_WIDTH), .din14_WIDTH(din14_WIDTH), .din15_WIDTH(din15_WIDTH), .din16_WIDTH(din16_WIDTH),
//   .din17_WIDTH(din17_WIDTH), .dout_WIDTH(dout_WIDTH)
// ) u_sva (.*, .clk(tb_clk), .rst_n(tb_rst_n));