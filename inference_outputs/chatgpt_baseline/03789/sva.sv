module arithmetic_logic_unit_sva (
    input logic        clk,
    input logic [31:0] a,
    input logic [31:0] b,
    input logic [3:0]  aluc,
    input logic [31:0] result
);

    wire [31:0] addresult;
    wire [31:0] subresult;

    assign addresult = a + b;
    assign subresult = a - b;

    // AND opcodes drive the bitwise AND of a and b.
    check_and_opcodes: assert property (
        @(posedge clk) ((aluc == 4'b0001) || (aluc == 4'b1001)) |-> (result == (a & b))
    );

    // OR opcodes drive the bitwise OR of a and b.
    check_or_opcodes: assert property (
        @(posedge clk) ((aluc == 4'b0101) || (aluc == 4'b1101)) |-> (result == (a | b))
    );

    // XOR opcodes drive the bitwise XOR of a and b.
    check_xor_opcodes: assert property (
        @(posedge clk) ((aluc == 4'b1010) || (aluc == 4'b0010)) |-> (result == (a ^ b))
    );

    // LUI opcodes drive zero-extended b[15:0].
    check_lui_opcodes: assert property (
        @(posedge clk) ((aluc == 4'b0110) || (aluc == 4'b1110)) |-> (result == {16'b0, b[15:0]})
    );

    // ADD opcodes drive a + b.
    check_add_opcodes: assert property (
        @(posedge clk) ((aluc == 4'b0000) || (aluc == 4'b1000)) |-> (result == addresult)
    );

    // SUB opcodes drive a - b.
    check_sub_opcodes: assert property (
        @(posedge clk) ((aluc == 4'b0100) || (aluc == 4'b1100)) |-> (result == subresult)
    );

    // SLL opcode drives b shifted left by a.
    check_sll_opcode: assert property (
        @(posedge clk) (aluc == 4'b0011) |-> (result == (b << a))
    );

    // SRL opcode drives b shifted right by a.
    check_srl_opcode: assert property (
        @(posedge clk) (aluc == 4'b0111) |-> (result == (b >> a))
    );

    // SRA opcode drives arithmetic right shift of signed b by a.
    check_sra_opcode: assert property (
        @(posedge clk) (aluc == 4'b1111) |-> (result == ($signed(b) >>> a))
    );

    // The default opcode 1011 also drives a + b.
    check_default_add_opcode: assert property (
        @(posedge clk) (aluc == 4'b1011) |-> (result == addresult)
    );

endmodule