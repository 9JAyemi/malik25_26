module ripple_adder(
    input [7:0] a,b,
    output [7:0] sum,
    output carry_out
);

wire [8:0] c;
wire [7:0] s;

assign c[0] = 1'b0;
genvar i;
generate
    for (i = 0; i < 8; i = i + 1) begin : adder_loop
        full_adder fa(
            .a(a[i]),
            .b(b[i]),
            .c_in(c[i]),
            .s(s[i]),
            .c_out(c[i+1])
        );
    end
endgenerate

assign carry_out = c[8];
assign sum = s;

endmodule

module full_adder(
    input a,b,c_in,
    output s,c_out
);

assign s = a ^ b ^ c_in;
assign c_out = (a & b) | (c_in & (a ^ b));

endmodule

module top_module(
    input [7:0] a,b,
    output [7:0] sum
);

wire carry_out;
ripple_adder ra(
    .a(a),
    .b(b),
    .sum(sum),
    .carry_out(carry_out)
);

endmodule