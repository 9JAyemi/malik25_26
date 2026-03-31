module arithmetic_logic_unit_sva (
    input logic        clk,
    input logic [31:0] a,
    input logic [31:0] b,
    input logic [3:0]  aluc,
    input logic [31:0] result
);

    // AND opcode drives the bitwise AND result.
    check_and_opcode: assert property (
        @(posedge clk) (aluc == 4'b0001) |-> (result == (a & b))
    );

    // OR opcode drives the bitwise OR result.
    check_or_opcode: assert property (
        @(posedge clk) (aluc == 4'b0101) |-> (result == (a | b))
    );

    // XOR opcode drives the bitwise XOR result.
    check_xor_opcode: assert property (
        @(posedge clk) (aluc == 4'b1010) |-> (result == (a ^ b))
    );

    // ADD opcode drives the addition result.
    check_add_opcode: assert property (
        @(posedge clk) (aluc == 4'b0000) |-> (result == (a + b))
    );

    // SUB opcode drives the subtraction result.
    check_sub_opcode: assert property (
        @(posedge clk) (aluc == 4'b0100) |-> (result == (a - b))
    );

    // SLL opcode drives the logical left shift result.
    check_sll_opcode: assert property (
        @(posedge clk) (aluc == 4'b0011) |-> (result == (b << a))
    );

    // SRL opcode drives the logical right shift result.
    check_srl_opcode: assert property (
        @(posedge clk) (aluc == 4'b0111) |-> (result == (b >> a))
    );

    // SRA opcode drives the arithmetic right shift result.
    check_sra_opcode: assert property (
        @(posedge clk) (aluc == 4'b1111) |-> (result == ($signed(b) >>> a))
    );

    // LUI opcode drives the upper-immediate result.
    check_lui_opcode: assert property (
        @(posedge clk) (aluc == 4'b0110) |-> (result == {16'b0, b[15:0]})
    );

    // Unrecognized opcode falls through to ADD.
    check_default_add: assert property (
        @(posedge clk) ((aluc != 4'b0001) &&
                        (aluc != 4'b0101) &&
                        (aluc != 4'b1010) &&
                        (aluc != 4'b0000) &&
                        (aluc != 4'b0100) &&
                        (aluc != 4'b0011) &&
                        (aluc != 4'b0111) &&
                        (aluc != 4'b1111) &&
                        (aluc != 4'b0110) &&
                        (aluc != 4'b1101) &&
                        (aluc != 4'b1100)) |-> (result == (a + b))
    );

endmodule