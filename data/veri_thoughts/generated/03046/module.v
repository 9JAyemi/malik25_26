module EtherCAT_master (
  input clk,
  input rst,
  input [7:0] tx_data,
  input tx_valid,
  output reg [7:0] rx_data,
  input rx_valid,
  output reg tx_ready,
  input rx_ready
);

always @(posedge clk or posedge rst) begin
  if (rst) begin
    tx_ready <= 1'b0;
  end else begin
    tx_ready <= tx_valid && rx_ready;
  end
end

always @(posedge clk or posedge rst) begin
  if (rst) begin
    rx_data <= 8'b0;
  end else begin
    if (rx_valid) begin
      rx_data <= rx_data;
    end
  end
end

endmodule

module EtherCAT_slave (
  input clk,
  input rst,
  output reg [7:0] tx_data,
  output reg tx_valid,
  input [7:0] rx_data,
  output reg rx_valid,
  input tx_ready,
  output reg rx_ready
);

always @(posedge clk or posedge rst) begin
  if (rst) begin
    tx_data <= 8'b0;
    tx_valid <= 1'b0;
  end else begin
    if (tx_ready) begin
      tx_data <= tx_data;
      tx_valid <= 1'b1;
    end else begin
      tx_valid <= 1'b0;
    end
  end
end

always @(posedge clk or posedge rst) begin
  if (rst) begin
    rx_ready <= 1'b0;
    rx_valid <= 1'b0;
  end else begin
    rx_ready <= 1'b1;
    rx_valid <= tx_ready;
  end
end

endmodule