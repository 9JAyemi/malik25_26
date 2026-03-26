
module top_module (
    input clk,
    input reset,
    input [7:0] a,
    input [7:0] b,
    input select,
    output [7:0] sum,
    output [7:0] diff,
    output [7:0] abs_diff
);

    // Instantiate the adder module
    adder_module adder(
        .a(a),
        .b(b),
        .sum(sum)
    );

    // Calculate the difference between a and b
    assign diff = a - b;

    // Instantiate the multiplexer module
    mux2to1_module mux(
        .a(sum),
        .b(diff),
        .select(select),
        .out(abs_diff)
    );

endmodule
module adder_module (
    input [7:0] a,
    input [7:0] b,
    output reg [7:0] sum
);

    always @(*) begin
        sum = a + b;
    end

endmodule
module mux2to1_module (
    input [7:0] a,
    input [7:0] b,
    input select,
    output reg [7:0] out
);

    always @(select or a or b) begin
        out = (select == 1'b0) ? a : b;
    end

endmodule