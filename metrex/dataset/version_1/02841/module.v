module add3 (
    input [3:0] A,
    input [3:0] B,
    input [3:0] C,
    output [4:0] S
);

    wire [4:0] sum1, sum2;

    add2 a1(.A(A), .B(B), .S(sum1));
    add2 a2(.A(sum1[3:0]), .B(C), .S(sum2));
    assign S = {sum2[4], sum2[3:0]};

endmodule

module add2 (
    input [3:0] A,
    input [3:0] B,
    output [4:0] S
);

    wire [3:0] sum;
    wire carry;

    assign sum = A + B;
    assign carry = (sum >= 10);

    assign S = {carry, sum};

endmodule

