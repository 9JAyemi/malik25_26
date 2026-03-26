module johnson_counter #(
  parameter n = 4 // number of output signals
)(
  input clk,
  input rst,
  output reg [n-1:0] out
);


reg [n-1:0] q;

always @(posedge clk, posedge rst) begin
  if (rst) begin
    q <= 0;
    out <= 0;
  end
  else begin
    q <= {q[n-2:0], q[n-1]};
    out <= q;
  end
end

endmodule