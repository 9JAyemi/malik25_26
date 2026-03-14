module memory_protection_blocks (
  input [31:0] in1, 
  input in2, 
  output reg out 
);

parameter start_address = 32'h00000000; 
parameter end_address = 32'h000000FF;

always @(*) begin
  if (in1 >= start_address && in1 <= end_address && in2 == 1'b1) begin
    out = 1'b1; 
  end else begin
    out = 1'b0; 
  end
end

endmodule
