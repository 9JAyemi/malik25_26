
module adder4bit(
    input [3:0] A,
    input [3:0] B,
    input cin,
    output [3:0] S,
    output cout
);

wire c0, c1, c2;

// Instantiate the full adder modules
full_adder fa0(.a(A[0]), .b(B[0]), .cin(cin), .sum(S[0]), .cout(c0));
full_adder fa1(.a(A[1]), .b(B[1]), .cin(c0), .sum(S[1]), .cout(c1));
full_adder fa2(.a(A[2]), .b(B[2]), .cin(c1), .sum(S[2]), .cout(c2));
full_adder fa3(.a(A[3]), .b(B[3]), .cin(c2), .sum(S[3]), .cout(cout));

endmodule

module full_adder(
    input a,
    input b,
    input cin,
    output sum,
    output cout
);

// Calculate the sum and carry-out values
assign sum = a ^ b ^ cin;
assign cout = (a & b) | (a & cin) | (b & cin);

endmodule
