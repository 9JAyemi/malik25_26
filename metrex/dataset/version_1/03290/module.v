module top_module (
    input [31:0] a,
    input [31:0] b,
    input [7:0] ctrl,
    output [31:0] result,
    output overflow
);

wire [31:0] alu_output;
wire [7:0] adder_output;
wire overflow_adder;

// Instantiate 32-bit ALU
alu_32bit alu_inst (
    .a(a),
    .b(b),
    .ctrl(ctrl[3:0]),
    .result(alu_output)
);

// Instantiate 8-bit adder/subtractor
adder_subtractor_8bit adder_inst (
    .a(a[7:0]),
    .b(b[7:0]),
    .ctrl(ctrl[7]),
    .result(adder_output),
    .overflow(overflow_adder)
);

// Bitwise AND operation
assign result = alu_output & {24'b0, adder_output};
assign overflow = overflow_adder;

endmodule

module alu_32bit (
    input [31:0] a,
    input [31:0] b,
    input [3:0] ctrl,
    output [31:0] result
);

reg [31:0] result_reg;

always @(*) begin
    case(ctrl)
        4'b0000: result_reg = a + b;
        4'b0001: result_reg = a - b;
        4'b0010: result_reg = a & b;
        4'b0011: result_reg = a | b;
        4'b0100: result_reg = a ^ b;
        4'b0101: result_reg = a << 1;
        4'b0110: result_reg = a >> 1;
        default: result_reg = 32'b0;
    endcase
end

assign result = result_reg;

endmodule

module adder_subtractor_8bit (
    input [7:0] a,
    input [7:0] b,
    input ctrl,
    output [7:0] result,
    output overflow
);

reg [7:0] result_reg;
reg overflow_reg;

always @(*) begin
    if (ctrl) begin
        result_reg = a - b;
        overflow_reg = (a[7] & ~b[7] & result_reg[7]) | (~a[7] & b[7] & ~result_reg[7]);
    end else begin
        result_reg = a + b;
        overflow_reg = (a[7] & b[7] & ~result_reg[7]) | (~a[7] & ~b[7] & result_reg[7]);
    end
end

assign result = result_reg;
assign overflow = overflow_reg;

endmodule