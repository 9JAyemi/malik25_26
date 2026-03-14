module my_dff (
  input clk,
  input d,
  output reg q
);

always @(posedge clk) begin
  q <= d;
end

endmodule

module shift_register (
  input clk,
  input [3:0] data_in,
  output [3:0] data_out
);

wire [3:0] dff_out;

my_dff dff0 (.clk(clk), .d(data_in[0]), .q(dff_out[0]));
my_dff dff1 (.clk(clk), .d(dff_out[0]), .q(dff_out[1]));
my_dff dff2 (.clk(clk), .d(dff_out[1]), .q(dff_out[2]));
my_dff dff3 (.clk(clk), .d(dff_out[2]), .q(dff_out[3]));

assign data_out = dff_out;

endmodule