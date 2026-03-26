
module xor_gate(
    input a, b,
    output out
    );

    assign out = a ^ b;

endmodule

module four_output_module(
    input a, b, c,
    output w, x, y, z
    );

    assign w = a;
    assign x = b;
    assign y = c;
    assign z = a & b;

endmodule

module final_module(
    input clk, a, b, c,
    output reg out
    );

    wire xor_out;
    wire w, x, y, z;

    xor_gate xor_inst(
        .a(a),
        .b(b),
        .out(xor_out)
    );

    four_output_module four_out_inst(
        .a(a),
        .b(b),
        .c(c),
        .w(w),
        .x(x),
        .y(y),
        .z(z)
    );

    always @(posedge clk)
        out <= xor_out & w & y;

endmodule

module top_module(
    input clk,
    input a, b, c,
    output w, x, y, z,
    output out
);

    wire xor_out;

    final_module final_inst(
        .clk(clk),
        .a(a),
        .b(b),
        .c(c),
        .out(out)
    );

    four_output_module four_out_inst(
        .a(a),
        .b(b),
        .c(c),
        .w(w),
        .x(x),
        .y(y),
        .z(z)
    );

endmodule
