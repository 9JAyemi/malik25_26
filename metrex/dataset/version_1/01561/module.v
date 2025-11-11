
module carry_select_adder (
    input [31:0] a, b,
    input cin,
    output cout,
    output [31:0] sum
);

wire [31:0] ripple_carry_out_0;
wire [31:0] ripple_carry_out_1;

rca32 rca32_0 (
    .a(a),
    .b(b),
    .cin(cin),
    .cout(ripple_carry_out_0)
);

rca32 rca32_1 (
    .a(a),
    .b(b),
    .cin(~cin),
    .cout(ripple_carry_out_1)
);

mux32 mux32_0 (
    .a(ripple_carry_out_0),
    .b(ripple_carry_out_1),
    .s(cin),
    .y(sum)
);

or_gate or_gate_0 (
    .a(ripple_carry_out_0[31]),
    .b(ripple_carry_out_1[31]),
    .y(cout)
);

endmodule
module mux32 (
    input [31:0] a, b,
    input s,
    output [31:0] y
);

assign y = s ? b : a;

endmodule
module or_gate (
    input a, b,
    output y
);

assign y = a | b;

endmodule
module rca32 (
    input [31:0] a, b,
    input cin,
    output [31:0] cout
);

wire [31:0] carry;

assign carry[0] = cin;

genvar i;
generate
    for (i = 0; i < 31; i = i + 1) begin
        full_adder fa (
            .a(a[i]),
            .b(b[i]),
            .cin(carry[i]),
            .cout(carry[i + 1]),
            .sum(cout[i])
        );
    end
endgenerate

assign cout[31] = carry[31];

endmodule
module full_adder (
    input a, b, cin,
    output cout, sum
);

assign sum = a ^ b ^ cin;
assign cout = (a & b) | (b & cin) | (a & cin);

endmodule