
module top_module (
    input [2:0] a,
    input [2:0] b,
    output [2:0] out_or_bitwise,
    output out_or_logical,
    output [5:0] out_not,
    output [7:0] s,
    output overflow
    );


    // Carry look-ahead adder for addition and overflow detection
    wire [3:0] a_ext, b_ext;
    assign a_ext = {1'b0, a};
    assign b_ext = {1'b0, b};

    wire [3:0] add_out;
    wire add_carry_out;
    cla_adder_4bit adder(.a(a_ext), .b(b_ext), .sum(add_out), .carry_out(add_carry_out));

    assign s = {add_carry_out, add_out};
    assign overflow = add_carry_out;

    // Combinational circuit for bitwise-OR and logical-OR operations
    assign out_or_bitwise = a | b;
    assign out_or_logical = |out_or_bitwise;

    // Functional module for 2's complement addition
    wire [2:0] add_in;
    assign add_in = out_or_bitwise;
    wire [2:0] add_out2;
    wire add_overflow;
    twos_comp_adder adder2(.a(add_in), .b_in(out_or_logical), .sum(add_out2), .overflow(add_overflow));

    // Output
    assign out_not = {~b, ~a};

endmodule
module cla_adder_4bit (
    input [3:0] a,
    input [3:0] b,
    output [3:0] sum,
    output carry_out
);

    wire [3:0] g, p, c;
    assign g[0] = a[0] & b[0];
    assign p[0] = a[0] ^ b[0];
    assign g[1] = a[1] & b[1];
    assign p[1] = a[1] ^ b[1];
    assign g[2] = a[2] & b[2];
    assign p[2] = a[2] ^ b[2];
    assign g[3] = a[3] & b[3];
    assign p[3] = a[3] ^ b[3];
    assign c[0] = g[0];
    assign c[1] = g[1] | (p[1] & c[0]);
    assign c[2] = g[2] | (p[2] & c[1]);
    assign carry_out = g[3] | (p[3] & c[2]);

    assign sum[0] = p[0] ^ c[0];
    assign sum[1] = p[1] ^ c[1];
    assign sum[2] = p[2] ^ c[2];
    assign sum[3] = p[3] ^ carry_out;

endmodule
module twos_comp_adder (
    input [2:0] a,
    input b_in,
    output [2:0] sum,
    output overflow
    );

    wire [2:0] b;
    assign b = b_in ? 3'b111 : 3'b000;

    wire [3:0] a_ext, b_ext;
    assign a_ext = {1'b0, a};
    assign b_ext = {1'b0, b};

    wire [3:0] add;
    wire carry_out;
    cla_adder_4bit adder(.a(a_ext), .b(~b_ext), .sum(add), .carry_out(carry_out));

    assign sum = add[2:0];
    assign overflow = carry_out;

endmodule