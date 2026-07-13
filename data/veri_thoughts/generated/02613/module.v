module ripple_carry_adder (
  input [3:0] A,
  input [3:0] B,
  input cin,
  output [3:0] sum,
  output cout
);

  wire [4:0] carry;
  
  assign carry[0] = cin;
  
  genvar i;
  generate
    for (i = 0; i < 4; i = i + 1) begin : adder
      full_adder fa (
        .a(A[i]),
        .b(B[i]),
        .cin(carry[i]),
        .sum(sum[i]),
        .cout(carry[i+1])
      );
    end
  endgenerate
  
  assign cout = carry[4];
  
endmodule

module full_adder (
  input a,
  input b,
  input cin,
  output sum,
  output cout
);

  assign sum = a ^ b ^ cin;
  assign cout = (a & b) | (a & cin) | (b & cin);
  
endmodule