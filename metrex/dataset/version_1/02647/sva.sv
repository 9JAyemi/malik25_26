// SVA for uart_tx
// Bind this file to the DUT: bind uart_tx uart_tx_sva u_uart_tx_sva (.*);

module uart_tx_sva (
  input logic         clk,
  input logic         reset_n,
  input logic         clk_en,
  input logic         begintransfer,
  input logic         tx_wr_strobe,
  input logic         status_wr_strobe,
  input logic         do_force_break,
  input logic  [7:0]  tx_data,
  input logic [15:0]  baud_divisor,
  input logic         tx_overrun,
  input logic         tx_ready,
  input logic         tx_shift_empty,
  input logic         txd,

  // internal
  input logic         baud_clk_en,
  input logic [15:0]  baud_rate_counter,
  input logic         baud_rate_counter_is_zero,
  input logic         do_load_shifter,
  input logic         do_shift,
  input logic         pre_txd,
  input logic         shift_done,
  input logic  [9:0]  tx_load_val,
  input logic         tx_shift_reg_out,
  input logic  [9:0]  tx_shift_register_contents,
  input logic         tx_wr_strobe_onset
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!reset_n);

  // Combinational equivalences
  assert property (tx_wr_strobe_onset == (tx_wr_strobe && begintransfer));
  assert property (shift_done == ~(|tx_shift_register_contents));
  assert property (tx_shift_reg_out == tx_shift_register_contents[0]);
  assert property (tx_load_val == {1'b1, tx_data, 1'b0});
  assert property (do_shift == (baud_clk_en && !shift_done && !do_load_shifter));
  assert property (baud_rate_counter_is_zero == (baud_rate_counter == 16'd0));
  assert property (clk_en |-> (baud_clk_en == baud_rate_counter_is_zero));
  assert property (do_load_shifter |-> !do_shift);

  // Reset values hold while in reset
  assert property (!reset_n |-> (do_load_shifter==0 && tx_ready==1 && tx_overrun==0 &&
                                 tx_shift_empty==1 && baud_rate_counter==0 &&
                                 baud_clk_en==0 && pre_txd==1 && txd==1));

  // Hold when clk_en is low (for clk_en-gated regs)
  assert property (!clk_en |=> (tx_ready==$past(tx_ready) &&
                                tx_overrun==$past(tx_overrun) &&
                                tx_shift_empty==$past(tx_shift_empty) &&
                                baud_rate_counter==$past(baud_rate_counter) &&
                                baud_clk_en==$past(baud_clk_en) &&
                                txd==$past(txd) &&
                                tx_shift_register_contents==$past(tx_shift_register_contents)));

  // do_load_shifter registered from (~tx_ready && shift_done)
  assert property (clk_en |=> do_load_shifter == $past((!tx_ready) && shift_done));

  // tx_ready state machine
  assert property (clk_en && tx_wr_strobe_onset |=> tx_ready==0);
  assert property (clk_en && !tx_wr_strobe_onset && do_load_shifter |=> tx_ready==1);
  assert property (clk_en && !(tx_wr_strobe_onset || do_load_shifter) |=> tx_ready==$past(tx_ready));

  // tx_overrun set/clear
  assert property (clk_en && status_wr_strobe |=> tx_overrun==0);
  assert property (clk_en && !status_wr_strobe && (!tx_ready && tx_wr_strobe_onset) |=> tx_overrun==1);
  assert property (clk_en && !(status_wr_strobe || (!tx_ready && tx_wr_strobe_onset)) |=> tx_overrun==$past(tx_overrun));

  // tx_shift_empty mirrors tx_ready && shift_done
  assert property (clk_en |=> tx_shift_empty == $past(tx_ready && shift_done));

  // Baud-rate counter behavior
  assert property (clk_en && (baud_rate_counter_is_zero || do_load_shifter)
                   |=> baud_rate_counter == $past(baud_divisor));
  assert property (clk_en && !(baud_rate_counter_is_zero || do_load_shifter)
                   |=> baud_rate_counter == $past(baud_rate_counter) - 16'd1);

  // Shift register load/shift/hold
  assert property (clk_en && do_load_shifter
                   |=> tx_shift_register_contents == $past(tx_load_val));
  assert property (clk_en && !do_load_shifter && do_shift
                   |=> tx_shift_register_contents == {1'b0, $past(tx_shift_register_contents)[9:1]});
  assert property (clk_en && !do_load_shifter && !do_shift
                   |=> tx_shift_register_contents == $past(tx_shift_register_contents));

  // pre_txd captures current LSB while shifting; holds when done
  assert property (!shift_done |=> pre_txd == $past(tx_shift_reg_out));
  assert property ( shift_done |=> pre_txd == $past(pre_txd));

  // txd registered, and forced low on break
  assert property (clk_en |=> txd == $past(pre_txd & ~do_force_break));
  assert property (clk_en && do_force_break |=> txd==0);

  // --------------- Coverage ---------------

  // Cover a full byte transmit: write, load, 10 shifts, done and ready
  cover property (clk_en && tx_wr_strobe_onset
                  ##1 clk_en && do_load_shifter
                  ##[1:$] (clk_en && do_shift)[*10]
                  ##[0:$] (shift_done && tx_ready));

  // Cover overrun set then cleared
  cover property (clk_en && !tx_ready && tx_wr_strobe_onset ##1 tx_overrun ##[1:$] (clk_en && status_wr_strobe) ##1 !tx_overrun);

  // Cover break forcing line low
  cover property (clk_en && do_force_break ##1 txd==0);

  // Cover baud counter reload by zero and by load
  cover property (clk_en && baud_rate_counter_is_zero ##1 baud_clk_en);
  cover property (clk_en && do_load_shifter ##1 baud_rate_counter == baud_divisor);

endmodule

// Example bind (connects internal signals)
// bind uart_tx uart_tx_sva u_uart_tx_sva (.*);