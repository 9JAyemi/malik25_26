
module fifo (
  input clk, // clock signal
  input rst, // reset signal
  input [7:0] data_in, // input data
  input wr_en, // write enable signal
  output reg [7:0] data_out, // output data
  input rd_en, // read enable signal
  output reg full = 0, // FIFO full signal
  output reg empty = 1 // FIFO empty signal
);

parameter DEPTH = 8; // FIFO depth
  
reg [7:0] mem [DEPTH-1:0]; // internal memory array
reg [2:0] wr_ptr = 0, rd_ptr = 0; // write and read pointers
reg [2:0] count = 0; // number of elements in the FIFO

always @(posedge clk) begin
  if (rst) begin
    wr_ptr <= 0;
    rd_ptr <= 0;
    count <= 0;
    empty <= 1;
    full <= 0;
  end else begin
    if (wr_en & ~full) begin // Corrected the condition
      mem[wr_ptr] <= data_in;
      wr_ptr <= wr_ptr + 1;
      if (wr_ptr == DEPTH) begin
        wr_ptr <= 0;
      end
      count <= count + 1;
      empty <= 0;
      if (count == DEPTH) begin
        full <= 1;
      end
    end
    if (rd_en & ~empty) begin // Corrected the condition
      data_out <= mem[rd_ptr];
      rd_ptr <= rd_ptr + 1;
      if (rd_ptr == DEPTH) begin
        rd_ptr <= 0;
      end
      count <= count - 1;
      full <= 0;
      if (count == 0) begin
        empty <= 1;
      end
    end
  end
end

endmodule