// SVA for wb_readback_mux_16LE
// Bindable assertions and coverage focused on handshake and 16-bit LE readback behavior.

module wb_readback_mux_16LE_sva
(
  input  logic        wb_clk_i,
  input  logic        wb_rst_i,
  input  logic        wb_stb_i,
  input  logic [15:0] wb_adr_i,
  input  logic [15:0] wb_dat_o,
  input  logic        wb_ack_o,

  // internal reg from DUT (bind hierarchically)
  input  logic [31:0] data,

  // word inputs (for data mapping checks)
  input  logic [31:0] word00, word01, word02, word03,
  input  logic [31:0] word04, word05, word06, word07,
  input  logic [31:0] word08, word09, word10, word11,
  input  logic [31:0] word12, word13, word14, word15
);

  function automatic logic [31:0] sel_word(input logic [3:0] idx);
    case (idx)
      4'd0:  sel_word = word00;
      4'd1:  sel_word = word01;
      4'd2:  sel_word = word02;
      4'd3:  sel_word = word03;
      4'd4:  sel_word = word04;
      4'd5:  sel_word = word05;
      4'd6:  sel_word = word06;
      4'd7:  sel_word = word07;
      4'd8:  sel_word = word08;
      4'd9:  sel_word = word09;
      4'd10: sel_word = word10;
      4'd11: sel_word = word11;
      4'd12: sel_word = word12;
      4'd13: sel_word = word13;
      4'd14: sel_word = word14;
      4'd15: sel_word = word15;
    endcase
  endfunction

  wire ack_n = wb_stb_i & ~wb_ack_o;

  // reset behavior
  property p_ack_low_during_reset; @(posedge wb_clk_i) wb_rst_i |-> !wb_ack_o; endproperty
  assert property (p_ack_low_during_reset);

  default clocking cb @(posedge wb_clk_i); endclocking
  default disable iff (wb_rst_i);

  // ack relation and pulse shape
  assert property (wb_ack_o == $past(wb_stb_i & ~wb_ack_o));
  assert property (!(wb_ack_o && $past(wb_ack_o)));
  assert property (wb_ack_o |-> $past(wb_stb_i));
  assert property (!wb_stb_i |=> !wb_ack_o);

  // structural: output reflects data[15:0]
  assert property (wb_dat_o == data[15:0]);

  // data write enables
  assert property ((!ack_n) |=> data == $past(data));

  // low-half access loads full 32b from selected word
  assert property ((ack_n && !wb_adr_i[1]) |=> data == $past(sel_word(wb_adr_i[5:2])));

  // high-half access shifts high 16b down, leaves high 16b unchanged
  assert property ((ack_n && wb_adr_i[1]) |=> (data[15:0] == $past(data[31:16]) &&
                                               data[31:16] == $past(data[31:16])));

  // end-to-end data seen with ack_o
  assert property (wb_ack_o && $past(ack_n && !wb_adr_i[1])
                   |-> wb_dat_o == $past(sel_word(wb_adr_i[5:2]))[15:0]);
  assert property (wb_ack_o && $past(ack_n && wb_adr_i[1])
                   |-> wb_dat_o == $past(data[31:16]));

  // coverage
  cover property (ack_n && !wb_adr_i[1]);
  cover property (ack_n &&  wb_adr_i[1]);
  genvar i;
  generate
    for (i=0; i<16; i++) begin : COV_ADDRS
      cover property (ack_n && !wb_adr_i[1] && wb_adr_i[5:2] == i[3:0]);
    end
  endgenerate
  // cover a low-half followed by a high-half sometime later
  sequence lo_then_hi; (ack_n && !wb_adr_i[1]) ##[1:8] (ack_n && wb_adr_i[1]); endsequence
  cover property (lo_then_hi);

endmodule

// Example bind (add to a package or testbench):
// bind wb_readback_mux_16LE wb_readback_mux_16LE_sva sva (
//   .wb_clk_i(wb_clk_i), .wb_rst_i(wb_rst_i), .wb_stb_i(wb_stb_i),
//   .wb_adr_i(wb_adr_i), .wb_dat_o(wb_dat_o), .wb_ack_o(wb_ack_o),
//   .data(data),
//   .word00(word00), .word01(word01), .word02(word02), .word03(word03),
//   .word04(word04), .word05(word05), .word06(word06), .word07(word07),
//   .word08(word08), .word09(word09), .word10(word10), .word11(word11),
//   .word12(word12), .word13(word13), .word14(word14), .word15(word15)
// );