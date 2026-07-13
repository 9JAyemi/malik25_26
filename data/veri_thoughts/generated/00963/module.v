module adder (
  input [3:0] A,
  input [3:0] B,
  input C,
  output reg [3:0] S
);

  always @(*) begin
    if (C == 0) begin
      S = A + B;
    end else begin
      S = A - B;
    end
  end

endmodule

