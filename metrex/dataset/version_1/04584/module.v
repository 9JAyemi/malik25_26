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

module ripple_carry_adder (
    input [3:0] A,
    input [3:0] B,
    output [4:0] sum
);

    wire [3:0] carry;
    full_adder fa0(.a(A[0]), .b(B[0]), .cin(1'b0), .sum(sum[0]), .cout(carry[0]));
    full_adder fa1(.a(A[1]), .b(B[1]), .cin(carry[0]), .sum(sum[1]), .cout(carry[1]));
    full_adder fa2(.a(A[2]), .b(B[2]), .cin(carry[1]), .sum(sum[2]), .cout(carry[2]));
    full_adder fa3(.a(A[3]), .b(B[3]), .cin(carry[2]), .sum(sum[3]), .cout(sum[4]));

endmodule