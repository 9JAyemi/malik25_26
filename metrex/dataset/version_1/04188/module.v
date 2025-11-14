module uart_transmitter (
  input clk,
  input rst,
  input [7:0] data_in,
  output tx
);

  reg [9:0] shift_reg;
  reg start_bit;
  reg stop_bit;
  reg [3:0] bit_count;

  always @ (posedge clk) begin
    if (rst) begin
      shift_reg <= 10'b0;
      bit_count <= 4'b0;
      start_bit <= 1'b0;
      stop_bit <= 1'b1;
    end else begin
      if (bit_count == 4'b0) begin
        shift_reg <= {start_bit, data_in, stop_bit};
        bit_count <= 4'b1;
      end else if (bit_count < 4'b10) begin
        shift_reg <= {shift_reg[8:0], 1'b0};
        bit_count <= bit_count + 1;
      end else begin
        shift_reg <= {shift_reg[8:0], 1'b1};
        bit_count <= 4'b0;
      end
    end
  end

  assign tx = shift_reg[0];

endmodule

module uart_receiver (
  input clk,
  input rst,
  input rx,
  output reg [7:0] data_out
);

  reg [9:0] shift_reg;
  reg start_bit;
  reg stop_bit;
  reg [3:0] bit_count;

  always @ (posedge clk) begin
    if (rst) begin
      shift_reg <= 10'b0;
      bit_count <= 4'b0;
      start_bit <= 1'b0;
      stop_bit <= 1'b0;
      data_out <= 8'b0;
    end else begin
      if (bit_count == 4'b0) begin
        start_bit <= rx;
        bit_count <= 4'b1;
      end else if (bit_count < 4'b10) begin
        shift_reg <= {shift_reg[8:0], rx};
        bit_count <= bit_count + 1;
      end else begin
        stop_bit <= rx;
        data_out <= shift_reg[8:1];
        bit_count <= 4'b0;
      end
    end
  end

endmodule