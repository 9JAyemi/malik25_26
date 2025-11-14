module bw_r_idct_array(
  input we,
  input clk,
  input [32:0] wr_data,
  input [6:0] addr,
  input [3:0] dec_wrway_y,
  input [1:0] way,
  output reg [32:0] rd_data
);

  // Declare array
  reg [32:0] array[511:0]  ;
  

  
  // Read/write operation
  always @(negedge clk) begin
    if (we) begin
      array[addr] <= wr_data;
    end else begin
      rd_data <= array[addr];
    end
  end
  
endmodule