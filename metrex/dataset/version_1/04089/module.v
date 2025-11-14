module data_store(
  input [15:0] data_in,
  input enable,
  input clk,
  output reg [15:0] data_out
);

always @(posedge clk) begin
  if (enable) begin
    data_out <= data_in;
  end
end

endmodule