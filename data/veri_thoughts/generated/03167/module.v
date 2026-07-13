module calculator(clk, a, b, op, result);

  input clk;
  input [7:0] a, b, op;
  output reg [7:0] result;
  
  always @(posedge clk) begin
    if (op == 0) begin
      result <= a + b;
    end else begin
      result <= a - b;
    end
  end
  
endmodule
