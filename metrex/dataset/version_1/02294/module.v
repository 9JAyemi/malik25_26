module dual_edge_triggered_ff (
  input clk,
  input reset,
  input data,
  output reg q
);

reg q1, q2;

always @(posedge clk) begin
  if (reset) begin
    q1 <= 1'b0;
    q2 <= 1'b0;
  end else begin
    q1 <= data;
    q2 <= q1;
  end
end

always @(negedge clk) begin
  if (reset) begin
    q <= 1'b0;
  end else begin
    q <= q2;
  end
end

endmodule
