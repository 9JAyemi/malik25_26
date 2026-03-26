module arithmetic_unit(
    input [15:0] a,
    input [15:0] b,
    input [1:0] op,
    output [31:0] result
);

    wire [15:0] sum;
    wire [15:0] diff;
    wire [15:0] and_result;

    assign sum = a + b;
    assign diff = a - b;
    assign and_result = a & b;

    // Priority Encoder to select operation based on op input
    wire [1:0] op_priority;
    assign op_priority = op == 2'b10 ? 2'b10 : op == 2'b01 ? 2'b01 : 2'b00;

    // Multiplexer to select appropriate operation
    wire [31:0] mux_result;
    assign mux_result = op_priority == 2'b10 ? {16'd0, and_result} : op_priority == 2'b01 ? {16'd0, diff} : {16'd0, sum};

    // Output result
    assign result = mux_result;

endmodule

module top_module(
    input [15:0] a,
    input [15:0] b,
    input [1:0] op,
    output [31:0] result
);

    arithmetic_unit au(
        .a(a),
        .b(b),
        .op(op),
        .result(result)
    );

endmodule