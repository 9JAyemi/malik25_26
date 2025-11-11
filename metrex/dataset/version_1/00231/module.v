
module bitwise_or_multiplier(
    input wire [7:0] byte1,
    input wire [7:0] byte2,
    output wire [15:0] result
);

    // Perform the bitwise OR operation on the two input bytes
    wire [7:0] or_result;
    assign or_result = byte1 | byte2;

    // Multiply the OR result by a constant value
    parameter constant_value = 42;
    assign result = or_result * constant_value;

endmodule

module top_module( 
    input wire [7:0] byte1,
    input wire [7:0] byte2,
    output wire [15:0] result );

    // Instantiate the bitwise OR multiplier module
    bitwise_or_multiplier or_multiplier(
        .byte1(byte1),
        .byte2(byte2),
        .result(result)
    );

endmodule
