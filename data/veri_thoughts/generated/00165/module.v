
module four_bit_adder(
  input [3:0] A,
  input [3:0] B,
  output reg [3:0] S,
  output reg C_out
);

  wire [4:0] carry;
  wire [4:0] sum;
  
  genvar i;
  generate
    for (i = 0; i < 4; i = i + 1) begin
      full_adder full_adder_inst(
        .A(A[i]),
        .B(B[i]),
        .C_in(carry[i]),
        .S(sum[i]),
        .C_out(carry[i+1])
      );
    end
  endgenerate
  
  assign carry[0] = 0;
  
  always @* begin
    S = sum[3:0];
    C_out = carry[4];
  end

endmodule
module full_adder (
  input A,
  input B,
  input C_in,
  output S,
  output C_out
);

  assign {C_out, S} = A + B + C_in;

endmodule