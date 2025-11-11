
module uart_rx (
  input clk,
  input rst,
  input rx,
  output reg [7:0] data_out
);

  reg [3:0] count;
  reg [7:0] shift_reg;
  reg start_bit;
  reg stop_bit;
  reg parity_bit;
  reg [1:0] parity;

  always @(posedge clk or posedge rst) begin
    if (rst) begin
      count <= 0;
      shift_reg <= 0;
      start_bit <= 0;
      stop_bit <= 1;
      parity_bit <= 0;
      parity <= 2'b00;
      data_out <= 0;
    end else begin
      if (count == 0) begin
        start_bit <= rx;
        count <= 11;
      end else if (count == 1) begin
        shift_reg <= {shift_reg[6:0], rx};
        parity_bit <= rx;
      end else if (count == 10) begin
        stop_bit <= rx;
      end else if (count == 11) begin
        data_out <= shift_reg;
      end
      count <= count - 1;
    end
  end

  always @* begin
    if (parity == 2'b00) begin
      parity_bit = 1;
    end else if (parity == 2'b01) begin
      parity_bit = ~shift_reg[0];
    end else if (parity == 2'b10) begin
      parity_bit = ~|shift_reg;
    end else if (parity == 2'b11) begin
      parity_bit = ~(shift_reg[0]^|shift_reg[7:1]);
    end
  end

  always @* begin
    if (parity == 2'b00) begin
      parity = 2'b01;
    end else if (parity == 2'b01) begin
      parity = 2'b10;
    end else if (parity == 2'b10) begin
      parity = 2'b11;
    end else if (parity == 2'b11) begin
      parity = 2'b00;
    end
  end

endmodule
