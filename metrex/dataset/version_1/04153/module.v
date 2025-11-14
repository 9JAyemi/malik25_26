
module CDC_Synchronizer (
  input [N-1:0] data_in,
  input clk_in,
  input rst_in,
  input clk_out,
  output [N-1:0] data_out,
  output rst_out
);

parameter N = 8; // number of bits in input and output data signals

reg [N-1:0] synchronized_data;
reg synchronized_reset;

always @(posedge clk_out) begin
  synchronized_data <= data_in;
  synchronized_reset <= rst_in;
end

reg [N-1:0] latched_data;
reg latched_reset;

always @(posedge clk_out) begin
  latched_data <= synchronized_data;
end

always @(posedge clk_out) begin
  latched_reset <= synchronized_reset;
end

assign data_out = latched_data;
assign rst_out = latched_reset;

endmodule