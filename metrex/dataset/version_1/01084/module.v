module multiplier (
  input [n-1:0] A,
  input [n-1:0] B,
  input mode,
  output reg [n-1:0] P
);

parameter n = 8; // number of bits in A and B

reg [n-1:0] partial_product;
reg [2*n-1:0] shifted_A;
reg [n:0] extended_A, extended_B;
integer i;

always @(*) begin
  if (mode == 0) begin // Unsigned multiplication
    partial_product = 0;
    for (i = 0; i < n; i = i + 1) begin
      if (B[i]) begin
        shifted_A = A << i;
        partial_product = partial_product + shifted_A[n-1:0];
      end
    end
  end else begin // Signed multiplication
    partial_product = 0;
    extended_A = {A[n-1], A};
    extended_B = {B[n-1], B};
    for (i = 0; i < n; i = i + 1) begin
      case ({extended_B[i+1], extended_B[i]})
        2'b01: partial_product <= partial_product - extended_A[n-1:0];
        2'b10: partial_product <= partial_product + extended_A[n-1:0];
        default: ; // do nothing
      endcase
      extended_A = extended_A << 1;
    end
  end
  P <= partial_product;
end

endmodule