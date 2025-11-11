module bluetooth_receiver (
  input clk,
  input reset,
  input [15:0] rx_in,
  output reg [7:0] data_out
);

  reg [15:0] demodulated_data;
  reg [7:0] decoded_data;
  reg [3:0] bit_counter;
  reg [15:0] carrier_signal;

  // Bluetooth demodulation
  always @ (posedge clk) begin
    if (reset) begin
      demodulated_data <= 16'b0000000000000000;
      carrier_signal <= 16'b0000000000000000;
    end else begin
      if (rx_in[15] != carrier_signal[15]) begin
        demodulated_data <= {demodulated_data[14:0], rx_in[15]};
      end
      carrier_signal <= {carrier_signal[14:0], rx_in[15]};
    end
  end

  // Bluetooth decoding scheme
  always @ (posedge clk) begin
    if (reset) begin
      decoded_data <= 8'b00000000;
      bit_counter <= 4'd0;
    end else begin
      if (bit_counter == 4'd3) begin
        decoded_data <= {demodulated_data[6], demodulated_data[5], demodulated_data[4], demodulated_data[3], demodulated_data[2], demodulated_data[1], demodulated_data[0]};
        bit_counter <= 4'd0;
      end else begin
        bit_counter <= bit_counter + 1;
      end
    end
  end

  // Output data
  always @ (posedge clk) begin
    if (reset) begin
      data_out <= 8'b00000000;
    end else begin
      data_out <= decoded_data;
    end
  end

endmodule