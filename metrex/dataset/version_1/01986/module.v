module adder(input [3:0] a, input [3:0] b, output reg [4:0] sum);

  always @(*) begin
    sum = a + b;
    if (sum > 15) sum = sum[3:0];
  end

endmodule