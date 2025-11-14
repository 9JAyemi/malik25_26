
module mod_operator (
  input [31:0] A,
  input [31:0] B,
  output reg [31:0] result
);

  always @(*) begin
    if (B == 0) begin
      result = 0;
    end else if (A < B) begin
      result = A;
    end else begin
      result = A - (A / B) * B;
    end
  end

endmodule