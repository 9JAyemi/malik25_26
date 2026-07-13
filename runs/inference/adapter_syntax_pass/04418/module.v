module xor_product (
    input clk,
    input reset,
    input [7:0] in_1,
    input [7:0] in_2,
    input select,
    output [7:0] xor_output,
    output [7:0] or_output
);

    wire [7:0] twos_comp;
    wire [7:0] adder_output;
    wire [7:0] xor_input;

    // 2-to-1 multiplexer to select between the two input values
    assign xor_input = select ? in_2 : in_1;

    // 8-bit adder to compute their sum
    adder adder_inst (
        .clk(clk),
        .reset(reset),
        .a(in_1),
        .b(in_2),
        .sum(adder_output)
    );

    // Functional block that performs a bitwise XOR operation
    assign xor_output = adder_output ^ xor_input;

    // Two's complement of the first input
    assign twos_comp = ~in_1 + 1;

    // Product of the two's complement of the first input and the second input
    assign or_output = twos_comp & in_2;

endmodule

// 8-bit adder module
module adder (
    input clk,
    input reset,
    input [7:0] a,
    input [7:0] b,
    output reg [7:0] sum
);

    always @(posedge clk) begin
        if (reset) begin
            sum <= 8'b0;
        end else begin
            sum <= a + b;
        end
    end

endmodule