
module register_module (
  input clk,
  output reg [3:0] A,
  output reg [3:0] B,
  output reg [3:0] C
);

  initial begin
    A = 0;
    B = 0;
    C = 0;
  end

  always @(posedge clk) begin
    #2 A = A + 1;
    #3 B = B - 1;
  end

  always @(A or B) begin
    C = A + B;
  end

endmodule