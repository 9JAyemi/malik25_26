// SVA for uart_transmitter and uart_receiver
// Bind these checkers to the DUTs to verify behavior and collect concise coverage.

module uart_transmitter_sva (
  input logic        clk, reset, din, baud_clk,
  input logic [7:0]  shift_reg,
  input logic        tx_busy,
  input logic        tx
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Reset state
  assert property (reset |=> (shift_reg==8'h00 && tx_busy==1'b0 && tx==1'b1));

  // No state/output changes without baud tick
  assert property (!baud_clk |-> $stable({shift_reg, tx_busy, tx}));

  // tx updates from previous MSB on each baud tick
  assert property (baud_clk |=> tx == $past(shift_reg[7]));

  // Load when idle on baud tick
  assert property ((baud_clk && !tx_busy) |=> (shift_reg == {7'b0,$past(din)} && tx_busy));

  // Shift left while busy on baud tick
  assert property ((baud_clk && tx_busy) |=> shift_reg == {$past(shift_reg[6:0]),1'b0});

  // Clear busy when (old) shift_reg is zero on a baud tick
  assert property ((baud_clk && tx_busy && shift_reg==8'h00) |=> !tx_busy);

  // Coverage
  cover property (baud_clk && !tx_busy && din==1'b0);
  cover property (baud_clk && !tx_busy && din==1'b1);
  cover property ($rose(tx_busy) ##[1:$] !tx_busy);
  cover property (baud_clk && tx_busy && shift_reg==8'h80);
endmodule


module uart_receiver_sva (
  input logic        clk, reset, rx, baud_clk,
  input logic [7:0]  shift_reg,
  input logic        rx_busy,
  input logic        dout
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Reset state
  assert property (reset |=> (shift_reg==8'h00 && rx_busy==1'b0 && dout==1'b0));

  // No state changes without baud tick
  assert property (!baud_clk |-> $stable({shift_reg, rx_busy}));

  // Start detect: rx low on baud tick when idle sets busy
  assert property ((baud_clk && !rx_busy && rx==1'b0) |=> rx_busy);

  // Shift while busy on baud tick
  assert property ((baud_clk && rx_busy) |=> shift_reg == {$past(shift_reg[6:0]), $past(rx)});

  // Clear busy when (old) shift_reg is zero on a baud tick
  assert property ((baud_clk && rx_busy && shift_reg==8'h00) |=> !rx_busy);

  // dout always mirrors MSB of shift_reg
  assert property (dout == shift_reg[7]);

  // Coverage
  cover property (baud_clk && !rx_busy && rx==1'b0);
  cover property ($rose(rx_busy) ##[1:$] !rx_busy);
  cover property (baud_clk && rx_busy && shift_reg[7]==1'b1);
endmodule


// Example binds (place in a testbench or a package included in simulation)
bind uart_transmitter uart_transmitter_sva tx_sva (
  .clk(clk), .reset(reset), .din(din), .baud_clk(baud_clk),
  .shift_reg(shift_reg), .tx_busy(tx_busy), .tx(tx)
);

bind uart_receiver uart_receiver_sva rx_sva (
  .clk(clk), .reset(reset), .rx(rx), .baud_clk(baud_clk),
  .shift_reg(shift_reg), .rx_busy(rx_busy), .dout(dout)
);