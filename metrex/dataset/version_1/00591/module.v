module binary_up_counter (
  input clk,
  output reg [3:0] out
);

parameter n = 4; // number of bits in the counter

reg [3:0] count;

always @(posedge clk) begin
  if (count == (2**n)-1) begin
    count <= 0;
  end else begin
    count <= count + 1;
  end
end

always @* begin
  out = count;
end

endmodule