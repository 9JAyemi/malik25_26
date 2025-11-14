
module wifi_transceiver (
  input clk,
  input reset,
  input [31:0] data_in,
  output [99:0] rx_packet,
  output [31:0] data_out,
  output [99:0] tx_packet,
  output tx_busy
);

  reg [31:0] data_buffer;
  reg [99:0] tx_packet_reg;
  reg tx_busy_reg;
  reg [31:0] rx_data;
  reg [31:0] rx_checksum;
  reg [31:0] calculated_checksum;

  assign tx_packet = tx_packet_reg;
  assign tx_busy = tx_busy_reg;
  assign data_out = rx_data;
  assign rx_packet[99:96] = 4'hF;
  assign rx_packet[95:64] = data_in ^ 32'hAAAAAAAA;
  assign rx_packet[63:32] = ~data_in;
  assign rx_packet[31:0] = data_in;

  always @(posedge clk or posedge reset) begin
    if (reset) begin
      data_buffer <= 32'h0;
      tx_packet_reg <= 100'h0;
      tx_busy_reg <= 1'b0;
    end else begin
      if (!tx_busy_reg) begin
        data_buffer <= data_in;
        tx_packet_reg[31:0] <= data_in;
        tx_packet_reg[63:32] <= ~data_in;
        tx_packet_reg[95:64] <= data_in ^ 32'hAAAAAAAA;
        tx_packet_reg[99:96] <= 4'hF;
        tx_busy_reg <= 1'b1;
      end else begin
        tx_busy_reg <= 1'b0;
      end
    end
  end

  always @(posedge clk or posedge reset) begin
    if (reset) begin
      rx_data <= 32'h0;
      rx_checksum <= 32'h0;
    end else begin
      rx_data <= rx_packet[31:0];
      rx_checksum <= rx_packet[63:32];
      calculated_checksum <= rx_data ^ rx_packet[95:64] ^ 32'hAAAAAAAA;
    end
  end

endmodule