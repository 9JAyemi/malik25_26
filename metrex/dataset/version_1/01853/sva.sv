// SVA for update_TAGRAM
// Bind this module to the DUT: bind update_TAGRAM update_TAGRAM_sva u_sva(.*);

module update_TAGRAM_sva (
  input clk_in,
  input srst,

  // inputs
  input [7:0] tx_length_dw,
  input [7:0] tx_tag,
  input       tx_ack0,
  input [7:0] tx_fmt_type,
  input [7:0] rx_length_dw_byte,
  input [7:0] rx_tag,
  input       rx_ack_reg,
  input [7:0] rx_fmt_type,

  // outputs
  input [7:0] tagram_data_a,
  input [7:0] tagram_address_a,
  input       tagram_wren_a,
  input [7:0] tagram_data_b,
  input       tagram_wren_b,
  input [7:0] tagram_address_b,
  input [4:0] read_tagram
);

  // -----------------------------------------
  // Port A: write-through of tx_* each cycle; wren function
  // -----------------------------------------
  // Address/Data register follow tx_* each clock
  assert property (@(posedge clk_in) disable iff (srst)
    tagram_address_a == $past(tx_tag) &&
    tagram_data_a    == $past(tx_length_dw)
  );

  // WREN_A equals its function of inputs
  assert property (@(posedge clk_in) disable iff (srst)
    tagram_wren_a == $past( tx_ack0 &&
                            (tx_fmt_type[4:0] == 5'b00000) &&
                            (tx_fmt_type[6]   == 1'b0) )
  );

  // When asserting WREN_A, inputs that drive it are known
  assert property (@(posedge clk_in) disable iff (srst)
    tagram_wren_a |-> !$isunknown($past({tx_ack0, tx_fmt_type[6], tx_fmt_type[4:0], tx_tag, tx_length_dw}))
  );

  // -----------------------------------------
  // Port B: reset, write/hold behavior, wren function
  // -----------------------------------------
  // During reset, address_b goes to 0 on next cycle
  assert property (@(posedge clk_in)
    srst |=> (tagram_address_b == 8'h00)
  );

  // Prefer wren_b low during reset (flags RTL hole if not)
  assert property (@(posedge clk_in)
    srst |-> (tagram_wren_b == 1'b0)
  );

  // When not in reset: wren_b mirrors rx_ack_reg
  assert property (@(posedge clk_in) disable iff (srst)
    tagram_wren_b == $past(rx_ack_reg)
  );

  // On ack, capture rx_tag/rx_length into address_b/data_b
  assert property (@(posedge clk_in) disable iff (srst)
    $past(rx_ack_reg) |-> (tagram_address_b == $past(rx_tag) &&
                           tagram_data_b    == $past(rx_length_dw_byte))
  );

  // When no ack, hold previous address/data
  assert property (@(posedge clk_in) disable iff (srst)
    !$past(rx_ack_reg) |-> (tagram_address_b == $past(tagram_address_b) &&
                            tagram_data_b    == $past(tagram_data_b))
  );

  // Inputs known when writing on B
  assert property (@(posedge clk_in) disable iff (srst)
    $past(rx_ack_reg) |-> !$isunknown($past({rx_tag, rx_length_dw_byte}))
  );

  // -----------------------------------------
  // read_tagram generation and pipeline
  // -----------------------------------------
  // read_tagram[0] equals its condition (rx_length>=0 is tautology)
  assert property (@(posedge clk_in) disable iff (srst)
    read_tagram[0] == $past( (rx_fmt_type[6:1] == 6'b100101) && rx_ack_reg )
  );

  // Shift pipeline for stages 1..4
  assert property (@(posedge clk_in) disable iff (srst)
    read_tagram[1] == $past(read_tagram[0]) &&
    read_tagram[2] == $past(read_tagram[1]) &&
    read_tagram[3] == $past(read_tagram[2]) &&
    read_tagram[4] == $past(read_tagram[3])
  );

  // Pipeline clears to zero within 5 cycles of reset assertion
  assert property (@(posedge clk_in)
    srst |-> ##[1:5] (read_tagram == 5'b0)
  );

  // -----------------------------------------
  // Key functional coverage
  // -----------------------------------------
  // Cover a Port A write enable
  cover property (@(posedge clk_in) disable iff (srst)
    tx_ack0 && (tx_fmt_type[4:0] == 5'b00000) && (tx_fmt_type[6] == 1'b0)
  );

  // Cover a Port B write enable
  cover property (@(posedge clk_in) disable iff (srst)
    rx_ack_reg
  );

  // Cover full read_tagram pulse propagation 0->4
  cover property (@(posedge clk_in) disable iff (srst)
    ((rx_fmt_type[6:1] == 6'b100101) && rx_ack_reg)
    ##1 read_tagram[0]
    ##1 read_tagram[1]
    ##1 read_tagram[2]
    ##1 read_tagram[3]
    ##1 read_tagram[4]
  );

  // Cover simultaneous writes on A and B
  cover property (@(posedge clk_in) disable iff (srst)
    rx_ack_reg &&
    tx_ack0 && (tx_fmt_type[4:0] == 5'b00000) && (tx_fmt_type[6] == 1'b0)
  );

endmodule