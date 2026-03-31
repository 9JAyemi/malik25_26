module arithmetic_logic_unit_sva (
    input logic        clk,
    input logic [31:0] a,
    input logic [31:0] b,
    input logic [3:0]  aluc,
    input logic [31:0] result
);

    // AND operations drive the AND of a and b.
    check_and_operation: assert property (
        @(posedge clk)
        ((aluc == 4'b0001) || (aluc == 4'b1001)) |-> (result == (a & b))
    );

    // OR operations drive the OR of a and b.
    check_or_operation: assert property (
        @(posedge clk)
        ((aluc == 4'b0101) || (aluc == 4'b1101)) |-> (result == (a | b))
    );

    // XOR operations drive the XOR of a and b.
    check_xor_operation: assert property (
        @(posedge clk)
        ((aluc == 4'b1010) || (aluc == 4'b0010)) |-> (result == (a ^ b))
    );

    // LUI operations drive the upper 16 bits of b.
    check_lui_operation: assert property (
        @(posedge clk)
        ((aluc == 4'b0110) || (aluc == 4'b1110)) |-> (result == {16'b0, b[15:0]})
    );

    // ADD operations drive the 32-bit sum of a and b.
    check_add_operation: assert property (
        @(posedge clk)
        ((aluc == 4'b0000) || (aluc == 4'b1000)) |-> (result == (a + b))
    );

    // SUB operations drive the 32-bit difference of a and b.
    check_sub_operation: assert property (
        @(posedge clk)
        ((aluc == 4'b0100) || (aluc == 4'b1100)) |-> (result == (a - b))
    );

    // SLL operations drive b shifted left by a.
    check_sll_operation: assert property (
        @(posedge clk)
        (aluc == 4'b0011) |-> (result == (b << a))
    );

    // SRL operations drive b shifted right by a.
    check_srl_operation: assert property (
        @(posedge clk)
        (aluc == 4'b0111) |-> (result == (b >> a))
    );

    // SRA operations drive b shifted right arithmetically by a.
    check_sra_operation: assert property (
        @(posedge clk)
        (aluc == 4'b1111) |-> (result == ($signed(b) >>> a))
    );

    // Unlisted ALU codes default to ADD behavior.
    check_default_add_operation: assert property (
        @(posedge clk)
        !((aluc == 4'b0001) || (aluc == 4'b1001) ||
          (aluc == 4'b0101) || (aluc == 4'b1101) ||
          (aluc == 4'b1010) || (aluc == 4'b0010) ||
          (aluc == 4'b0110) || (aluc == 4'b1110) ||
          (aluc == 4'b0000) || (aluc == 4'b1000) ||
          (aluc == 4'b0100) || (aluc == 4'b1100) ||
          (aluc == 4'b0011) || (aluc == 4'b0111) ||
          (aluc == 4'b1111)) |-> (result == (a + b))
    );

endmodule