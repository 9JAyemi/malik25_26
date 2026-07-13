module top_module (
    input [7:0] in1,
    input [7:0] in2,
    output [8:0] out,
    output [7:0] sum
);

    wire [7:0] xor_result;
    wire parity_bit;

    // Calculate XOR result
    assign xor_result = in1 ^ in2;

    // Calculate parity bit
    assign parity_bit = ^xor_result;

    // Concatenate parity bit with XOR result
    assign out = {parity_bit, xor_result};

    // Add input bytes and output byte to get sum
    adder adder_inst(.a(in1), .b(in2), .c(out), .sum(sum));

endmodule

// Additive functional module
module adder (
    input [7:0] a,
    input [7:0] b,
    input [8:0] c,
    output [7:0] sum
);

    reg [7:0] temp_sum;

    always @(*) begin
        temp_sum = a + b + c[8];
    end

    assign sum = temp_sum;

endmodule