module ir_sva (
    input logic clk,
    input logic ir_we,
    input logic [31:0] instr,
    input logic [5:0] opcode,
    input logic [4:0] reg1,
    input logic [4:0] reg2,
    input logic [4:0] reg3,
    input logic [31:0] sx16,
    input logic [31:0] zx16,
    input logic [31:0] hi16,
    input logic [31:0] sx16s2,
    input logic [31:0] sx26s2
);

    ///// Combinational mapping invariants from registered IR /////
    // hi16 upper 16 pack must equal {opcode, reg1, reg2}.
    map_hi16_fields: assert property (
        @(posedge clk) {opcode, reg1, reg2} == hi16[31:16]
    );

    // hi16 low 16 must be zero.
    hi16_low_zero: assert property (
        @(posedge clk) hi16[15:0] == 16'h0000
    );

    // zx16 upper 16 must be zero.
    zx16_upper_zero: assert property (
        @(posedge clk) zx16[31:16] == 16'h0000
    );

    // reg3 must match zx16[15:11].
    reg3_matches_zx16_slice: assert property (
        @(posedge clk) reg3 == zx16[15:11]
    );

    // sx16 lower 16 equals zx16 lower 16 (both are ir[15:0]).
    sx16_low_matches_zx16_low: assert property (
        @(posedge clk) sx16[15:0] == zx16[15:0]
    );

    // sx16 sign extension driven by bit 15 of immediate.
    sx16_sign_extend_from_bit15: assert property (
        @(posedge clk) sx16[31:16] == {16{zx16[15]}}
    );

    // sx16s2 low two bits must be zero.
    sx16s2_low_two_zero: assert property (
        @(posedge clk) sx16s2[1:0] == 2'b00
    );

    // sx16s2 middle [17:2] echoes immediate bits.
    sx16s2_mid_matches_lowimm: assert property (
        @(posedge clk) sx16s2[17:2] == zx16[15:0]
    );

    // sx16s2 sign extension driven by bit 15 of immediate.
    sx16s2_sign_extend_from_bit15: assert property (
        @(posedge clk) sx16s2[31:18] == {14{zx16[15]}}
    );

    // sx26s2 low two bits must be zero.
    sx26s2_low_two_zero: assert property (
        @(posedge clk) sx26s2[1:0] == 2'b00
    );

    // sx26s2 sign extension driven by bit 25 (available in hi16[25]).
    sx26s2_sign_extend_from_bit25: assert property (
        @(posedge clk) sx26s2[31:28] == {4{hi16[25]}}
    );

    // sx26s2 middle [27:2] equals concatenation of fields {ir[25:16], ir[15:11], ir[10:0]}.
    sx26s2_middle_matches_26imm: assert property (
        @(posedge clk) sx26s2[27:2] == {hi16[25:16], reg3, zx16[10:0]}
    );

    ///// Register write behavior on ir_we /////
    // On write, next-cycle {opcode,reg1,reg2} equals past instr[31:16].
    update_fields_on_ir_we: assert property (
        @(posedge clk) ir_we |=> {opcode, reg1, reg2} == $past(instr[31:16])
    );

    // On write, next-cycle reg3 equals past instr[15:11].
    update_reg3_on_ir_we: assert property (
        @(posedge clk) ir_we |=> reg3 == $past(instr[15:11])
    );

    // On write, next-cycle zx16 equals zero-extended past instr[15:0].
    update_zx16_on_ir_we: assert property (
        @(posedge clk) ir_we |=> zx16 == {16'h0000, $past(instr[15:0])}
    );

    // On write, next-cycle hi16 equals {past instr[31:16], 16'h0000}.
    update_hi16_on_ir_we: assert property (
        @(posedge clk) ir_we |=> hi16 == {$past(instr[31:16]), 16'h0000}
    );

    // On write, next-cycle sx16 equals sign-extended past instr[15:0].
    update_sx16_on_ir_we: assert property (
        @(posedge clk) ir_we |=> sx16 == {{16{$past(instr[15])}}, $past(instr[15:0])}
    );

    // On write, next-cycle sx16s2 equals sign-extended then <<2 of past instr[15:0].
    update_sx16s2_on_ir_we: assert property (
        @(posedge clk) ir_we |=> sx16s2 == {{14{$past(instr[15])}}, $past(instr[15:0]), 2'b00}
    );

    // On write, next-cycle sx26s2 equals sign-extended then <<2 of past instr[25:0].
    update_sx26s2_on_ir_we: assert property (
        @(posedge clk) ir_we |=> sx26s2 == {{4{$past(instr[25])}}, $past(instr[25:0]), 2'b00}
    );

endmodule