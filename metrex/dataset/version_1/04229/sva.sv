// SVA for uart
module uart_sva #(
  parameter int unsigned DIVISOR = 1
) (
  input  logic         clk,
  input  logic         reset_b,
  input  logic         cs_b,
  input  logic         a0,
  input  logic         rnw,
  input  logic         rxd,
  input  logic         txd,
  input  logic [15:0]  din,
  input  logic [15:0]  dout,

  input  logic [15:0]  rx_bit_cnt,
  input  logic [15:0]  tx_bit_cnt,
  input  logic [10:0]  tx_shift_reg,
  input  logic [9:0]   rx_shift_reg,
  input  logic         rxd1,
  input  logic         rxd2,
  input  logic         rx_full,
  input  logic [7:0]   rx_data,
  input  logic         rx_busy,
  input  logic         tx_busy
);

  // Reset values
  assert property (@(posedge clk) !reset_b |-> (tx_shift_reg == 11'b1));
  assert property (@(posedge clk) !reset_b |-> (rx_shift_reg == 10'b1111111111));

  // Basic mapping/invariants
  assert property (@(posedge clk) txd == tx_shift_reg[0]);
  assert property (@(posedge clk) a0  |-> (dout[15:8] == 8'h00 && dout[7:0] == rx_data));
  assert property (@(posedge clk) !a0 |-> (dout == {tx_busy, rx_full, 14'b0}));

  // Busy equivalences
  assert property (@(posedge clk) tx_busy == (tx_shift_reg != 11'b1));
  assert property (@(posedge clk) rx_busy == (rx_shift_reg != 10'b1111111111));

  // RX: start detect, shifting, complete, clear
  assert property (@(posedge clk) disable iff (!reset_b)
    (!rxd1 && rxd2 && !rx_busy) |=> (rx_shift_reg == 10'b0111111111 && rx_bit_cnt == (DIVISOR >> 1))
  );

  assert property (@(posedge clk) disable iff (!reset_b)
    (rx_busy && rx_shift_reg[0] && rx_bit_cnt > 0) |=> (rx_bit_cnt == $past(rx_bit_cnt) - 1 && rx_shift_reg == $past(rx_shift_reg))
  );

  assert property (@(posedge clk) disable iff (!reset_b)
    (rx_busy && rx_shift_reg[0] && rx_bit_cnt == 0) |=> (rx_bit_cnt == DIVISOR && rx_shift_reg == {$past(rxd1), $past(rx_shift_reg[9:1])})
  );

  assert property (@(posedge clk) disable iff (!reset_b)
    (!rx_shift_reg[0]) |=> (rx_full && rx_shift_reg == 10'b1111111111 && rx_data == $past(rx_shift_reg[9:2]))
  );

  assert property (@(posedge clk) disable iff (!reset_b)
    (!cs_b && rnw && a0) |=> (rx_full == 1'b0)
  );

  assert property (@(posedge clk) disable iff (!reset_b)
    (rx_full && !(!cs_b && rnw && a0)) |=> rx_full
  );

  // RX counter range while busy
  assert property (@(posedge clk) disable iff (!reset_b)
    (rx_busy && rx_shift_reg[0]) |-> (rx_bit_cnt <= DIVISOR)
  );

  // TX: accept/ignore write, shifting, counter behavior
  assert property (@(posedge clk) disable iff (!reset_b)
    (!cs_b && !rnw && a0 && !tx_busy) |=> (tx_shift_reg == {2'b11, $past(din[7:0]), 1'b0} && tx_bit_cnt == (DIVISOR - 1) && tx_busy)
  );

  assert property (@(posedge clk) disable iff (!reset_b)
    (!cs_b && !rnw && a0 && tx_busy) |=> (tx_shift_reg == $past(tx_shift_reg) && tx_bit_cnt == $past(tx_bit_cnt))
  );

  assert property (@(posedge clk) disable iff (!reset_b)
    (tx_busy && tx_bit_cnt > 0) |=> (tx_bit_cnt == $past(tx_bit_cnt) - 1 && tx_shift_reg == $past(tx_shift_reg))
  );

  assert property (@(posedge clk) disable iff (!reset_b)
    (tx_busy && tx_bit_cnt == 0) |=> (tx_bit_cnt == (DIVISOR - 1) && tx_shift_reg == {1'b0, $past(tx_shift_reg[10:1])})
  );

  // TX counter range while busy
  assert property (@(posedge clk) disable iff (!reset_b)
    tx_busy |-> (tx_bit_cnt <= (DIVISOR - 1))
  );

  // Coverage
  cover property (@(posedge clk) disable iff (!reset_b)
    (!cs_b && !rnw && a0 && !tx_busy) ##1
    (tx_busy && txd == 1'b0) ##[1:$]
    (tx_busy && tx_bit_cnt == 0)[*11]
  );

  cover property (@(posedge clk) disable iff (!reset_b)
    (!rxd1 && rxd2 && !rx_busy) ##[1:$] rx_full ##[1:$]
    (!cs_b && rnw && a0) ##1 !rx_full
  );

endmodule

// Bind into DUT
bind uart uart_sva #(.DIVISOR(DIVISOR)) uart_sva_i (
  .clk(clk),
  .reset_b(reset_b),
  .cs_b(cs_b),
  .a0(a0),
  .rnw(rnw),
  .rxd(rxd),
  .txd(txd),
  .din(din),
  .dout(dout),
  .rx_bit_cnt(rx_bit_cnt),
  .tx_bit_cnt(tx_bit_cnt),
  .tx_shift_reg(tx_shift_reg),
  .rx_shift_reg(rx_shift_reg),
  .rxd1(rxd1),
  .rxd2(rxd2),
  .rx_full(rx_full),
  .rx_data(rx_data),
  .rx_busy(rx_busy),
  .tx_busy(tx_busy)
);