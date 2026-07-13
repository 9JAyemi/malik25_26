module adder_subtractor(
    input [31:0] a,
    input [31:0] b,
    input sub,
    output [31:0] result
);

    assign result = sub ? a - b : a + b;

endmodule

module control_module(
    input select,
    output sub
);

    assign sub = select;

endmodule

module top_module(
    input [31:0] a,
    input [31:0] b,
    input sub,
    input select,
    output [31:0] final_output
);

    wire [31:0] adder_output;
    wire [31:0] subtractor_output;
    wire [31:0] inverted_subtractor_output;

    adder_subtractor adder(.a(a), .b(b), .sub(0), .result(adder_output));
    adder_subtractor subtractor(.a(a), .b(b), .sub(1), .result(subtractor_output));
    control_module control(.select(select), .sub(sub));
    assign inverted_subtractor_output = ~subtractor_output;

    assign final_output = select ? inverted_subtractor_output : adder_output;

endmodule