
module add_sub_module(
    input [31:0] a,
    input [31:0] b,
    input sub,
    output [31:0] sum
);

wire [31:0] carry;
wire [31:0] diff;

assign carry[0] = sub ? ~b[0] : b[0];

assign diff[0] = sub ? b[0] : ~b[0];

genvar i;
for (i = 1; i < 32; i = i + 1) begin : gen_full_adder
    full_adder fa(
        .a(a[i]),
        .b(b[i]),
        .cin(carry[i-1]),
        .sum(sum[i]),
        .cout(carry[i])
    );
end

assign sum[0] = sub ? a[0] ^ diff[0] : a[0] ^ carry[0];

endmodule
module full_adder(
    input a,
    input b,
    input cin,
    output wire sum,
    output wire cout
);

assign {cout, sum} = a + b + cin;

endmodule
module full_subtractor(
    input a,
    input b,
    input bin,
    output wire diff,
    output wire bout
);

assign {bout, diff} = a - b - bin;

endmodule