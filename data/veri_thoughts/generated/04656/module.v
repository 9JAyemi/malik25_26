module RingCounter #(
  parameter n = 4 // number of output signals
)(
  input clk,
  output [n-1:0] out
);


reg [n-1:0] count;

always @(posedge clk) begin
  count <= count + 1;
  if (count == 2**n) begin
    count <= 0;
  end
end

assign out = count; 

endmodule