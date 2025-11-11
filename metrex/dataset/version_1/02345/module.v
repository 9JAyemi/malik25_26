
module top_module (
    input [31:0] A,
    input [31:0] B,
    input [3:0] S,
    input [2:0] OPCODE,
    input CIN,
    output reg COUT,
    output reg [31:0] Y
);

reg [32:0] alu_output;

always @(*) begin
    case(OPCODE)
        3'b000: alu_output = A + B + CIN;
        3'b001: alu_output = A - B - (~CIN);
        3'b010: alu_output = A & B;
        3'b011: alu_output = A | B;
        3'b100: alu_output = A ^ B;
        3'b101: alu_output = (S == 0) ? A : (A << S[3:1]);
        3'b110: alu_output = (S == 0) ? B : (B << S[3:1]);
        default: alu_output = 0;
    endcase
end

always @(*) begin
    case(OPCODE)
        3'b000: Y = alu_output[31:0];
        3'b001: Y = alu_output[31:0];
        3'b010: Y = alu_output[31:0];
        3'b011: Y = alu_output[31:0];
        3'b100: Y = alu_output[31:0];
        3'b101: Y = alu_output[31:0];
        3'b110: Y = alu_output[31:0];
        default: Y = 0;
    endcase
end

always @(*) begin
    case(OPCODE)
        3'b000: COUT = (alu_output[32] == 1);
        3'b001: COUT = (alu_output[32] == 0);
        3'b010: COUT = 0;
        3'b011: COUT = 0;
        3'b100: COUT = 0;
        3'b101: COUT = (S != 0) ? (B[32 - S[3:1]] == 1) : (B[S[3:1] - 1] == 1);
        3'b110: COUT = (S != 0) ? (B[32 - S[3:1]] == 1) : (B[S[3:1] - 1] == 1);
        default: COUT = 0;
    endcase
end

endmodule