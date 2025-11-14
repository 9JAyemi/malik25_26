module RFID_Receiver #(
  parameter n = 8 // number of bits in the data signal
) (
  input rx,
  input clk,
  input rst,
  output reg [n-1:0] data_out,
  output reg valid
);

  
  reg [n-1:0] data_reg;
  reg [3:0] count;
  reg start_reg;
  
  always @(posedge clk) begin
    if (rst) begin
      count <= 0;
      data_reg <= 0;
      start_reg <= 0;
      valid <= 0;
    end
    else begin
      if (rx) begin
        if (count < n-1) begin
          count <= count + 1;
          data_reg[count] <= rx;
        end
        else begin
          count <= 0;
          data_out <= data_reg;
          valid <= 1;
          start_reg <= 1;
        end
      end
      else begin
        valid <= 0;
        if (start_reg) begin
          start_reg <= 0;
        end
      end
    end
  end
  
endmodule