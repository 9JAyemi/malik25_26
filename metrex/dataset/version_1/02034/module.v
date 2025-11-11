
module top_module (
    input clk,
    input reset,      // Synchronous active-high reset
    input [3:0] a,    // 4-bit input for ALU
    input [3:0] b,    // 4-bit input for ALU
    input [2:0] op,   // 3-bit control signal for ALU
    output [3:0] q // 4-bit output of the functional module
);

wire [3:0] alu_output;

alu alu_inst (
    .a(a),
    .b(b),
    .op(op),
    .result(alu_output)
);

twos_complement twos_complement_inst (
    .input_value(alu_output),
    .output_value(q)
);

endmodule

module alu (
    input [3:0] a,
    input [3:0] b,
    input [2:0] op,
    output reg [3:0] result
);

always @(*) begin
    case (op)
        3'b000: result = a + b;
        3'b001: result = a - b;
        3'b010: result = a & b;
        3'b011: result = a | b;
        3'b100: result = a ^ b;
        3'b101: result = a << 1;
        default: result = 4'b0;
    endcase
end

endmodule

module twos_complement (
    input [3:0] input_value,
    output reg [3:0] output_value
);

always @(*) begin
    output_value = ~input_value + 4'b0001;
end

endmodule
