module top_module_sva (
    input logic CLK,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [2:0] opcode,
    input logic zero
);
    // ALU operations
    // ALU result is correct for addition
    alu_addition: assert property (
        @(posedge CLK) $rose(opcode == 3'b000) |-> (A + B == top_module.alu_out)
    );
    // ALU result is correct for subtraction
    alu_subtraction: assert property (
        @(posedge CLK) $rose(opcode == 3'b001) |-> (A - B == top_module.alu_out)
    );
    // ALU result is correct for bitwise AND
    alu_and: assert property (
        @(posedge CLK) $rose(opcode == 3'b010) |-> (A & B == top_module.alu_out)
    );
    // ALU result is correct for bitwise OR
    alu_or: assert property (
        @(posedge CLK) $rose(opcode == 3'b011) |-> (A | B == top_module.alu_out)
    );
    // ALU result is correct for bitwise XOR
    alu_xor: assert property (
        @(posedge CLK) $rose(opcode == 3'b100) |-> (A ^ B == top_module.alu_out)
    );
    // ALU zero flag is set correctly for zero result
    alu_zero_flag: assert property (
        @(posedge CLK) $rose(opcode == 3'b000) |-> (top_module.alu_out == 4'b0000) |-> zero
    );
    // ALU zero flag is cleared correctly for non-zero result
    alu_zero_flag_clear: assert property (
        @(posedge CLK) $rose(opcode == 3'b000) |-> (top_module.alu_out != 4'b0000) |-> !zero
    );
    // Bitwise OR result is correct
    bitwise_or_result: assert property (
        @(posedge CLK) $rose(opcode == 3'b011) |-> (A | B == top_module.out)
    );
endmodule