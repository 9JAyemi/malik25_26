module four_bit_arithmetic_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [1:0] opcode,
    input logic [3:0] result
);

    // Opcode 00 selects the 4-bit sum.
    check_add_opcode_selects_sum: assert property (
        @(posedge clk) disable iff (1'b0)
        (opcode == 2'b00) |-> (result == (A + B))
    );

    // Opcode 01 selects the 4-bit difference.
    check_sub_opcode_selects_difference: assert property (
        @(posedge clk) disable iff (1'b0)
        (opcode == 2'b01) |-> (result == (A - B))
    );

    // Opcode 10 selects the bitwise AND.
    check_and_opcode_selects_and: assert property (
        @(posedge clk) disable iff (1'b0)
        (opcode == 2'b10) |-> (result == (A & B))
    );

    // Opcode 11 selects the bitwise OR.
    check_or_opcode_selects_or: assert property (
        @(posedge clk) disable iff (1'b0)
        (opcode == 2'b11) |-> (result == (A | B))
    );

endmodule