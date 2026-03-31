
module ripple_carry_adder (
    input [7:0] a,
    input [7:0] b,
    output [8:0] sum
);

wire [8:0] carry;
assign carry[0] = 1'b0;

genvar i;
generate
    for (i = 0; i < 8; i = i + 1) begin : adder
        full_adder fa(
            .a(a[i]),
            .b(b[i]),
            .cin(carry[i]),
            .sum(sum[i]),
            .cout(carry[i + 1])
        );
    end
endgenerate
assign sum[8] = carry[8];

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