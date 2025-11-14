module mux_functional (
    input [1:0] in,
    input select,
    output [1:0] out
);

    assign out = (select == 0) ? in[0] : in[1];

endmodule

module functional_module (
    input [1:0] in,
    output [1:0] out
);

    assign out = ~in;

endmodule

module top_module (
    input a,
    input b,
    input select,
    output [1:0] out
);

    wire [1:0] mux_out;
    mux_functional mux_inst (
        .in({a, b}),
        .select(select),
        .out(mux_out)
    );

    functional_module func_inst (
        .in(mux_out),
        .out(out)
    );

endmodule