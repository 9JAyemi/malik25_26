module nor_gate (
    input a, b,
    output out
);
    assign out = ~(a | b);
endmodule

module mux_2to1 (
    input a, b, sel,
    output out
);
    wire nor_a, nor_b, nor_sel;

    nor_gate nor1 (.a(a), .b(sel), .out(nor_a));
    nor_gate nor2 (.a(b), .b(~sel), .out(nor_b));
    nor_gate nor3 (.a(nor_a), .b(nor_b), .out(out));
endmodule

module subtractor (
    input [1:0] in,
    output [1:0] diff
);
    wire [1:0] sub_const = 2'b01;

    assign diff = in - sub_const;
endmodule

module top_module (
    input a, b,
    input sel,
    output [1:0] diff
);
    wire mux_out;

    mux_2to1 mux (.a(a), .b(b), .sel(sel), .out(mux_out));
    subtractor sub (.in({1'b0, mux_out}), .diff(diff));
endmodule