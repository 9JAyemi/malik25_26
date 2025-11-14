
module adder4 (
    input [3:0] A,
    input [3:0] B,
    input Cin,
    output [3:0] Sum,
    output Cout
);

    wire [4:0] carry;
    assign carry[0] = Cin;

    genvar i;
    generate
        for (i = 0; i < 4; i = i + 1) begin : adder_loop
            full_adder fa (
                .a(A[i]),
                .b(B[i]),
                .cin(carry[i]),
                .sum(Sum[i]),
                .cout(carry[i+1])
            );
        end
    endgenerate

    assign Cout = carry[4];

endmodule
module full_adder (
    input a,
    input b,
    input cin,
    output sum,
    output cout
);

    assign {cout, sum} = (a & b) | ((a^b) & cin) | ({1'b0, a} & {1'b0, b});

endmodule