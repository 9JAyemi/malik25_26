
module pcie_serdes (
  input ref_clk,
  input reset,
  input [31:0] tx_data,
  input tx_valid,
  output reg tx_ready,
  input rx_valid,
  output reg [31:0] rx_data,
  output reg rx_error
);

  // transmit data when valid and ready
  always @(posedge ref_clk) begin
    if (reset) begin
      tx_ready <= 1'b0;
    end else if (tx_valid && tx_ready) begin
      tx_ready <= 1'b0;
    end else if (!tx_valid && !tx_ready) begin
      tx_ready <= 1'b1;
    end
  end

  // receive data when valid
  always @(posedge ref_clk) begin
    if (reset) begin
      rx_data <= 32'b0;
      rx_error <= 1'b0;
    end else if (rx_valid) begin
      rx_data <= {rx_valid, rx_data[30:0]};
      rx_error <= rx_data[31];
    end
  end

endmodule