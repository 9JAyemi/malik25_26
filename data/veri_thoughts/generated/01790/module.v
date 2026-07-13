
module adder_mod (
    input [3:0] A,
    input [3:0] B,
    output [3:0] sum
);

    wire [3:0] carry;
    wire [3:0] full_sum;

    // Add each bit of A and B, storing the result in full_sum
    // and the carry out in carry
    full_adder fa0 (.a(A[0]), .b(B[0]), .cin(1'b0), .sum(full_sum[0]), .cout(carry[0]));
    full_adder fa1 (.a(A[1]), .b(B[1]), .cin(carry[0]), .sum(full_sum[1]), .cout(carry[1]));
    full_adder fa2 (.a(A[2]), .b(B[2]), .cin(carry[1]), .sum(full_sum[2]), .cout(carry[2]));
    full_adder fa3 (.a(A[3]), .b(B[3]), .cin(carry[2]), .sum(full_sum[3]), .cout(carry[3]));

    // The final sum is the 4 least significant bits of full_sum
    assign sum = full_sum[3:0];

endmodule

module full_adder (
    input a,
    input b,
    input cin,
    output sum,
    output cout
);

    assign {cout,sum} = a + b + cin;

endmodule
