module binary_add_sub (
  input [3:0] A,
  input [3:0] B,
  input mode,
  output reg [3:0] Y
);

  wire [3:0] B_neg;
  assign B_neg = (~B) + 1;

  always @* begin
    if (mode == 0) begin
      Y = A + B;
    end else begin
      Y = A + B_neg;
    end
  end

endmodule