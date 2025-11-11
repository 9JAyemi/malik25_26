// SVA for wireless_comm
// Bind this file to the DUT: bind wireless_comm wireless_comm_sva sva (.*,.tx_data_reg(tx_data_reg),.rx_data_reg(rx_data_reg));

module wireless_comm_sva (
  input        clk,
  input        reset_n,
  input  [7:0] tx_data,
  input        tx_en,
  input        rx_en,
  input  [7:0] rx_data,
  input        tx_busy,
  input  [7:0] tx_data_reg, // internal
  input  [7:0] rx_data_reg  // internal
);
  // Clocking and reset guards
  default clocking cb @(posedge clk); endclocking

  // Asynchronous reset forces zeros at clock boundaries
  // (checked every clk even while reset active)
  assert property (@cb !reset_n |-> (tx_busy==0 && tx_data_reg==8'h00 && rx_data_reg==8'h00 && rx_data==8'h00))
    else $error("Reset did not clear DUT to zeros");

  // Output connection
  assert property (@cb rx_data == rx_data_reg)
    else $error("rx_data not equal to rx_data_reg");

  // No X/Z on outputs when out of reset
  assert property (@cb reset_n |-> !$isunknown({tx_busy, rx_data}))
    else $error("X/Z detected on outputs");

  // tx_busy mirrors tx_en (1-cycle latency due to flop sampling semantics)
  assert property (@cb (reset_n && $past(reset_n)) |-> (tx_busy == $past(tx_en)))
    else $error("tx_busy does not mirror prior tx_en");

  // Transmit data capture/hold
  assert property (@cb (reset_n && $past(reset_n) && $past(tx_en)) |-> (tx_data_reg == $past(tx_data)))
    else $error("tx_data_reg did not capture tx_data");
  assert property (@cb (reset_n && $past(reset_n) && !$past(tx_en)) |-> (tx_data_reg == $past(tx_data_reg)))
    else $error("tx_data_reg changed without tx_en");

  // Receive data increment/hold (8-bit wrap-around)
  assert property (@cb (reset_n && $past(reset_n) && $past(rx_en)) |-> (rx_data_reg == $past(rx_data_reg)+8'd1))
    else $error("rx_data_reg did not increment on rx_en");
  assert property (@cb (reset_n && $past(reset_n) && !$past(rx_en)) |-> (rx_data_reg == $past(rx_data_reg)))
    else $error("rx_data_reg changed without rx_en");

  // Coverage
  cover property (@cb reset_n && $past(reset_n) && !$past(tx_en) && tx_en); // tx start
  cover property (@cb reset_n && $past(reset_n) && $past(tx_en) && (tx_data_reg == $past(tx_data)) && tx_busy); // tx capture+busy
  cover property (@cb reset_n && $past(reset_n) && $past(rx_en) && (rx_data_reg == $past(rx_data_reg)+8'd1)); // rx increment
  cover property (@cb reset_n && $past(reset_n) && $past(rx_en) && ($past(rx_data_reg)==8'hFF) && (rx_data_reg==8'h00)); // rx wrap
  cover property (@cb reset_n && $past(reset_n) && $past(tx_en) && $past(rx_en)); // concurrent tx and rx activity
endmodule

// Bind into DUT (place in a file compiled with the DUT or in a testbench file)
// bind wireless_comm wireless_comm_sva sva (.*,.tx_data_reg(tx_data_reg),.rx_data_reg(rx_data_reg));