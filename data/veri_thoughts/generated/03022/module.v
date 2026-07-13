module ring_counter (
  input clk,
  output reg [m-1:0] out
);

parameter m = 4; // number of flip-flops in the counter

reg [m-1:0] counter;

always @(posedge clk) begin
  if (counter == {m{1'b1}}) begin
    counter <= {m{1'b0}};
  end else begin
    counter <= {counter[m-2:0], counter[m-1]};
  end
end

initial begin
    out <= 0;
end

always @* begin
    out = counter;
end

endmodule