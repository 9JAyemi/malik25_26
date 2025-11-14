module fifo #(
  parameter depth = 8, // depth of the memory block
  parameter data_width = 8 // width of the data
)(
  input clk,
  input reset,
  input write_en,
  input [data_width-1:0] data_in,
  input read_en,
  output reg [data_width-1:0] data_out
);


reg [data_width-1:0] mem [0:depth-1]; // data storage array
reg [$clog2(depth):0] write_ptr = 0; // write pointer
reg [$clog2(depth):0] read_ptr = 0; // read pointer
reg [$clog2(depth):0] count = 0; // number of data items in the memory block

always @(posedge clk or posedge reset) begin
  if (reset) begin
    write_ptr <= 0;
    read_ptr <= 0;
    count <= 0;
  end else begin
    if (write_en && count < depth) begin
      mem[write_ptr] <= data_in;
      write_ptr <= write_ptr + 1;
      count <= count + 1;
    end
    if (read_en && count > 0) begin
      data_out <= mem[read_ptr];
      read_ptr <= read_ptr + 1;
      count <= count - 1;
    end
  end
end

endmodule