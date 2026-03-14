
module four_bit_adder(
    input [3:0] A,
    input [3:0] B,
    input Cin,
    output [3:0] Sum,
    output Cout
);
    
    wire c1, c2, c3;
    one_bit_adder fa1(.a(A[0]), .b(B[0]), .cin(Cin), .sum(Sum[0]), .cout(c1));
    one_bit_adder fa2(.a(A[1]), .b(B[1]), .cin(c1), .sum(Sum[1]), .cout(c2));
    one_bit_adder fa3(.a(A[2]), .b(B[2]), .cin(c2), .sum(Sum[2]), .cout(c3));
    one_bit_adder fa4(.a(A[3]), .b(B[3]), .cin(c3), .sum(Sum[3]), .cout(Cout));
    
endmodule
module one_bit_adder(
    input a,
    input b,
    input cin,
    output sum,
    output cout
);

    assign sum = a ^ b ^ cin;
    assign cout = (a & b) | (b & cin) | (a & cin);

endmodule