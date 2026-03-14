
module top_module (
    input [2:0] a,         // 3-bit input vector a
    input [2:0] b,         // 3-bit input vector b
    input sel_logic_or,   // Select input for logical OR or bitwise OR
    input sel_inverse,    // Select input for regular or inverse input vectors
    output [2:0] out_or,   // Output from logical OR module
    output [2:0] out_bitwise,  // Output from bitwise OR module
    output [5:0] out_not   // Output for inverses of input vectors
);

    wire [2:0] a_int, b_int;
    wire [2:0] out_or_int, out_bitwise_int;

    assign a_int = sel_inverse ? ~a : a;
    assign b_int = sel_inverse ? ~b : b;

    // Instantiate the logical OR module
    or_logic_module u_or_logic (
        .a(a_int),
        .b(b_int),
        .out(out_or_int)
    );

    // Instantiate the bitwise OR module
    or_bitwise_module u_or_bitwise (
        .a(a_int),
        .b(b_int),
        .out(out_bitwise_int)
    );

    // Combinational logic for inverses
    assign out_not[5:3] = ~b;
    assign out_not[2:0] = ~a;

    // Select between logical OR and bitwise OR
    assign out_or = sel_logic_or ? out_or_int : 3'b0;
    assign out_bitwise = ~sel_logic_or ? out_bitwise_int : 3'b0;

endmodule
module or_logic_module (
    input [2:0] a,
    input [2:0] b,
    output [2:0] out
);
    assign out = a | b;
endmodule
module or_bitwise_module (
    input [2:0] a,
    input [2:0] b,
    output [2:0] out
);
    assign out = a | b;
endmodule