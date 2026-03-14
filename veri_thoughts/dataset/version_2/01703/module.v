
module mux_multiply (
    input [3:0] in_0,
    input [3:0] in_1,
    input sel,
    output [7:0] out
);

    wire [3:0] selected_input;
    wire [7:0] product;

    // 2-to-1 multiplexer
    mux2to1 mux (
        .in_0(in_0),
        .in_1(in_1),
        .sel(sel),
        .out(selected_input)
    );

    // Arithmetic module for multiplication
    multiplier mult (
        .in_0(selected_input),
        .in_1(selected_input),
        .out(product)
    );

    assign out = product;

endmodule
module mux2to1 (
    input [3:0] in_0,
    input [3:0] in_1,
    input sel,
    output [3:0] out
);

    assign out = sel ? in_1 : in_0;

endmodule
module multiplier (
    input [3:0] in_0,
    input [3:0] in_1,
    output [7:0] out
);

    assign out = in_0 * in_1;

endmodule