module adder_4bit_with_cin (
  input [3:0] a,
  input [3:0] b,
  input cin,
  output reg [3:0] out,
  output reg cout
);

  always @(*) begin
    out[0] = a[0] ^ b[0] ^ cin;
    out[1] = a[1] ^ b[1] ^ (a[0] & b[0]) | (a[0] ^ b[0]) & cin;
    out[2] = a[2] ^ b[2] ^ (a[1] & b[1]) | (a[1] ^ b[1]) & (a[0] | b[0]) | (a[0] & b[0] & cin);
    out[3] = a[3] ^ b[3] ^ (a[2] & b[2]) | (a[2] ^ b[2]) & (a[1] | b[1]) | (a[1] & b[1] & (a[0] | b[0])) | (a[0] & b[0] & cin);
    if (out > 4'b1111) begin
      out = out[3:0];
      cout = 1;
    end
    else begin
      cout = 0;
    end
  end
  
endmodule
