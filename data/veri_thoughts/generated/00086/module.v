module barrel_shifter_16bit (
    input [15:0] D,
    input [3:0] shift_ctrl,
    output reg [15:0] Q
);
    always @(*) begin
        case(shift_ctrl)
            4'b0000: Q = D << 1;
            4'b0001: Q = D << 2;
            4'b0010: Q = D << 4;
            4'b0011: Q = D << 8;
            4'b0100: Q = D >> 1;
            4'b0101: Q = D >> 2;
            4'b0110: Q = D >> 4;
            4'b0111: Q = D >> 8;
            default: Q = D;
        endcase
    end
endmodule

module alu_32bit (
    input [31:0] a,
    input [31:0] b,
    input [3:0] ctrl,
    output reg [31:0] result
);
    always @(*) begin
        case(ctrl)
            4'b0000: result = a + b;
            4'b0001: result = a - b;
            4'b0010: result = a & b;
            4'b0011: result = a | b;
            4'b0100: result = a ^ b;
            default: result = a;
        endcase
    end
endmodule

module top_module (
    input [15:0] D,
    input [3:0] shift_ctrl,
    input [31:0] a,
    input [31:0] b,
    input [3:0] alu_ctrl,
    output reg [31:0] result
);

    // 16-bit barrel shifter
    wire [15:0] shifted_D;
    barrel_shifter_16bit bs16 (
        .D(D),
        .shift_ctrl(shift_ctrl),
        .Q(shifted_D)
    );

    // 32-bit ALU
    wire [31:0] alu_result;
    alu_32bit alu32 (
        .a(a),
        .b(b),
        .ctrl(alu_ctrl),
        .result(alu_result)
    );

    // Bitwise OR module
    wire [31:0] or_result;
    assign or_result = shifted_D | alu_result;

    // Output
    always @* begin
        result = or_result;
    end

endmodule