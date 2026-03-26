
module retiming_blocks #(
  parameter n = 8 // number of input and output signals
)(
  input [n-1:0] in,
  output [n-1:0] out,
  input clk
);


reg [n-1:0] reg_in;
reg [n-1:0] reg_out;

integer i;

always @(posedge clk) begin
  for (i = 0; i < n; i = i + 1) begin
    reg_in[i] <= in[i];
  end
end

always @(*) begin
  for (i = 0; i < n; i = i + 1) begin
    reg_out[i] = reg_in[i];
  end
end

assign out = reg_out;

endmodule
