// SVA for wifi_transceiver
// Bind into DUT; checks key protocol/encoding, pipeline, and coverage.

module wifi_transceiver_sva (
  input  logic        clk,
  input  logic        reset,
  input  logic [31:0] data_in,
  input  logic [99:0] rx_packet,
  input  logic [31:0] data_out,
  input  logic [99:0] tx_packet,
  input  logic        tx_busy,
  // internal regs for stronger checking
  input  logic [31:0] rx_data,
  input  logic [31:0] rx_checksum,
  input  logic [31:0] calculated_checksum
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Reset values
  assert property (reset |-> (tx_busy==1'b0 && tx_packet==100'h0 && data_out==32'h0));

  // tx_busy must toggle every cycle (1-cycle pulse)
  assert property (tx_busy == !$past(tx_busy));
  assert property (tx_busy |-> ##1 !tx_busy);

  // Transmit packet build on rising busy (when previous was idle)
  assert property (
    $past(tx_busy)==1'b0 |-> ( tx_busy
      && tx_packet[31:0]   == $past(data_in)
      && tx_packet[63:32]  == ~$past(data_in)
      && tx_packet[95:64]  == ($past(data_in) ^ 32'hAAAA_AAAA)
      && tx_packet[99:96]  == 4'hF )
  );

  // When busy deasserts, tx_packet holds value
  assert property ($past(tx_busy)==1'b1 |-> (!tx_busy && $stable(tx_packet)));

  // Receive path: combinational mapping
  assert property (rx_packet[31:0]  == data_in);
  assert property (rx_packet[63:32] == ~data_in);
  assert property (rx_packet[95:64] == (data_in ^ 32'hAAAA_AAAA));
  assert property (rx_packet[99:96] == 4'hF);

  // Receive pipeline registers
  assert property (data_out     == $past(rx_packet[31:0]));
  assert property (rx_data      == $past(rx_packet[31:0]));
  assert property (rx_checksum  == $past(rx_packet[63:32]));

  // Calculated checksum timing
  assert property (calculated_checksum == ($past(rx_data) ^ $past(rx_packet[95:64]) ^ 32'hAAAA_AAAA));

  // Basic functional coverage
  cover property (!reset ##1 tx_busy ##1 !tx_busy);                         // busy pulse
  cover property ($past(tx_busy)==0 && tx_busy && tx_packet[99:96]==4'hF);  // tx build observed
  cover property (data_out == $past(data_in));                              // rx pipeline observed
endmodule

bind wifi_transceiver wifi_transceiver_sva i_wifi_transceiver_sva (
  .clk(clk),
  .reset(reset),
  .data_in(data_in),
  .rx_packet(rx_packet),
  .data_out(data_out),
  .tx_packet(tx_packet),
  .tx_busy(tx_busy),
  .rx_data(rx_data),
  .rx_checksum(rx_checksum),
  .calculated_checksum(calculated_checksum)
);