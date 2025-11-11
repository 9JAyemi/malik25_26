
module SPM #(
  parameter depth = 16, // size of the memory block
  parameter data_width = 8 // width of each data element in bits
)(
  input clk,
  input write_en,
  input read_en,
  input [clogb2(depth)-1:0] addr, 
  input [data_width-1:0] data_in,
  output reg [data_width-1:0] data_out
);


// memory array
reg [data_width-1:0] mem [0:depth-1];

// Calculate the logarithm of depth using a constant expression
parameter log2_depth = $clog2(depth);

always @(posedge clk) begin
  if (write_en) begin
    mem[addr] <= data_in;
  end
  if (read_en) begin
    data_out <= mem[addr];
  end
end

function integer clogb2;
  input integer depth;
  integer cnt;
  begin
    cnt = 0;
    while (depth > 0) begin
      depth = depth >> 1;
      cnt = cnt + 1;
    end
    clogb2 = cnt - 1;
  end
endfunction

endmodule
