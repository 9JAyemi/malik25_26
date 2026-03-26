module adder_32bit(
  input [31:0] A,
  input [31:0] B,
  input Cin,
  output [31:0] Sum,
  output Cout
  );

  wire [31:0] carry; // intermediate carry values
  wire [31:0] sum; // intermediate sum values

  // full adder for bit 0
  full_adder fa0(A[0], B[0], Cin, sum[0], carry[0]);

  // carry chain for bits 1-30
  genvar i;
  generate
    for (i = 1; i < 31; i = i + 1) begin
      full_adder fa(
        A[i], B[i], carry[i-1], sum[i], carry[i]);
    end
  endgenerate

  // full adder for bit 31 with Cout as output
  full_adder fa31(A[31], B[31], carry[30], Sum[31], Cout);

  // assign intermediate sum values to output Sum
  assign Sum = sum;

endmodule

// full adder module
module full_adder(
  input A,
  input B,
  input Cin,
  output Sum,
  output Cout
  );

  assign Sum = A ^ B ^ Cin;
  assign Cout = (A & B) | (Cin & (A ^ B));

endmodule