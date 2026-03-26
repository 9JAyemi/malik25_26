module adder(
    input [7:0] A,
    input [7:0] B,
    output [7:0] sum
);

    wire [7:0] carry;

    // first full adder
    full_adder FA0(
        .a(A[0]),
        .b(B[0]),
        .c_in(1'b0),
        .sum(sum[0]),
        .c_out(carry[0])
    );

    // remaining full adders
    generate
        genvar i;
        for (i = 1; i < 8; i = i + 1) begin : FA_GEN
            full_adder FA(
                .a(A[i]),
                .b(B[i]),
                .c_in(carry[i-1]),
                .sum(sum[i]),
                .c_out(carry[i])
            );
        end
    endgenerate

endmodule

// full adder module
module full_adder(
    input a,
    input b,
    input c_in,
    output sum,
    output c_out
);

    assign sum = a ^ b ^ c_in;
    assign c_out = (a & b) | (a & c_in) | (b & c_in);

endmodule