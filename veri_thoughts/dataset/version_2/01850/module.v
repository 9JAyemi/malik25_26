module counter_4bit(
  input clk,
  input reset,
  input load,
  input [3:0] data,
  output reg [3:0] count
);

always @(posedge clk) begin
  if (reset) begin
    count <= 4'b0;
  end else if (load) begin
    count <= data;
  end else begin
    count <= count + 1;
  end
end

endmodule