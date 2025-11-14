module RFID #(
  parameter n = 8, // number of bits in the data signal
  parameter k = 4 // number of bits in the transmit signal
) (
  input [n-1:0] data_in,
  input clk,
  input rst,
  input start,
  output reg [k-1:0] tx
);

  reg [n-1:0] data_reg;
  reg [3:0] count;
  reg start_reg;
  
  always @(posedge clk) begin
    if (rst) begin
      count <= 0;
      tx <= 0;
      start_reg <= 0;
    end
    else begin
      if (start) begin
        start_reg <= 1;
        count <= 0;
        data_reg <= data_in;
        tx <= 1;
      end
      else if (start_reg) begin
        if (count < k-1) begin
          count <= count + 1;
          tx <= 0;
        end
        else begin
          count <= 0;
          tx <= 1;
          start_reg <= 0;
        end
      end
      else begin
        tx <= 0;
      end
    end
  end
  
endmodule

