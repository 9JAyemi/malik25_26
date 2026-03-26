module multiplier #(
  parameter n = 8 // number of bits in the input and output signals
)(
  input [n-1:0] a,
  input [n-1:0] b,
  output reg [n-1:0] result
);

parameter signed_mode = 1; // 1 for signed multiplication, 0 for unsigned multiplication.

reg [2*n-1:0] signed_a, signed_b;
wire [2*n-1:0] signed_result;

assign signed_result = signed_a * signed_b;

always @(*) begin
  if (signed_mode == 1) begin
    signed_a = {a[n-1], {n-1{a[n-1]}}, a};
    signed_b = {b[n-1], {n-1{b[n-1]}}, b};
    result <= signed_result[n-1:0];
  end else begin
    result <= a * b;
  end
end

endmodule