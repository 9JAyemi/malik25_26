module adder(A, B, sum);
  input [3:0] A, B;
  output reg [4:0] sum;
  
  always @* begin
    sum = A + B;
    if (sum > 15) begin
      sum = sum[3:0];
    end
  end
endmodule

