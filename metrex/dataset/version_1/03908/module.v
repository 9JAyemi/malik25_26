module top_module( 
    input [2:0] a,
    input [2:0] b,
    output [2:0] out_or_bitwise,
    output out_or_logical,
    output [5:0] out_not
);

    // instantiate the logical-OR and bitwise-OR module
    logic_or_bitwise_or_module lb_module(
        .a(a),
        .b(b),
        .out(out_or_bitwise)
    );

    // instantiate the inverter module
    inverter_module inv_module_a(
        .in(a),
        .out(out_not[2:0])
    );

    inverter_module inv_module_b(
        .in(b),
        .out(out_not[5:3])
    );

    // implement the logical-OR operation using XOR and AND gates
    assign out_or_logical = (a | b) == 3'b111 ? 1'b1 : 1'b0;

endmodule

// module for logical-OR and bitwise-OR
module logic_or_bitwise_or_module(
    input [2:0] a,
    input [2:0] b,
    output [2:0] out
);

    // implement the bitwise-OR operation using OR gates
    assign out = a | b;

endmodule

// module for inverter
module inverter_module(
    input [2:0] in,
    output [2:0] out
);

    // implement the inverter using NOT gates
    assign out = ~in;

endmodule