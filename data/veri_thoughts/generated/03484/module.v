module bitwise_and(
  input [7:0] a,
  input [7:0] b,
  output reg [7:0] out
);

  // initial block to set first bit of output vector
  initial begin
    if (a + b >= 128) begin
      out[0] <= 1;
    end else begin
      out[0] <= 0;
    end
  end

  // bitwise AND operation
  always @*
    out[7:1] = a[7:1] & b[7:1];

endmodule