
module ECC (
  input [n-1:0] in,
  output [m-1:0] out
);

parameter n = 8; // number of input bits
parameter m = 12; // number of output bits (n+p)
parameter p = 4; // number of parity bits

reg [n+p-1:0] codeword;
wire [p-1:0] parity;

// Generate parity bits
genvar i;
generate
  for (i = 0; i < p; i = i + 1) begin
    assign parity[i] = ^({1'b0, codeword[n+p-1:n]} >> (2**i-1));
  end
endgenerate

// Append parity bits to input bits
always @* begin
  codeword = {in, parity};
end

// Output codeword
assign out = codeword;

endmodule