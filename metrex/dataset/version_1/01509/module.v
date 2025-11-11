module binary_subtractor (
    input [7:0] a,
    input [7:0] b,
    output [8:0] diff
);

    wire [7:0] b_not;
    wire [8:0] sum;

    // Bitwise NOT operation on b
    assign b_not = ~b;

    // Binary adder module
    adder adder_inst (
        .a(a),
        .b(b_not),
        .sum(sum)
    );

    // Bitwise AND operation on a and b_not
    assign diff = {1'b0, a} & {1'b0, b_not};

endmodule

module adder (
    input [7:0] a,
    input [7:0] b,
    output [8:0] sum
);

    wire [7:0] carry;
    assign carry = {1'b0, a} + {1'b0, b};

    assign sum = carry + 1'b0;

endmodule

module top_module (
    input clk,
    input reset, // Synchronous active-high reset
    input [7:0] a, // 8-bit input
    input [7:0] b, // 8-bit input
    output [8:0] diff // 9-bit output with MSB representing the sign bit
);

    reg [8:0] diff_reg;
    wire [8:0] diff_wire;

    binary_subtractor sub_inst (
        .a(a),
        .b(b),
        .diff(diff_wire)
    );

    always @(posedge clk) begin
        if (reset) begin
            diff_reg <= 9'b1;
        end else begin
            diff_reg <= diff_wire;
        end
    end

    assign diff = diff_reg;

endmodule