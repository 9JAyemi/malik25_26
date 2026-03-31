module arithmetic_logic_unit_sva (
    input logic        clk,
    input logic [31:0] a,
    input logic [31:0] b,
    input logic [3:0]  aluc,
    input logic [31:0] result
);

// ALU opcode 0000 selects addition.
    check_add_result: assert property (
        @(posedge clk) (aluc == 4'b0000) |-> (result == (a + b))
    );

// ALU opcode 1000 selects addition.
    check_add_result_alt: assert property (
        @(posedge clk) (aluc == 4'b1000) |-> (result == (a + b))
    );

// ALU opcode 0100 selects subtraction.
    check_sub_result: assert property (
        @(posedge clk) (aluc == 4'b0100) |-> (result == (a - b))
    );

// ALU opcode 1100 selects subtraction.
    check_sub_result_alt: assert property (
        @(posedge clk) (aluc == 4'b1100) |-> (result == (a - b))
    );

// ALU opcode 0001 selects bitwise AND.
    check_and_result: assert property (
        @(posedge clk) (aluc == 4'b0001) |-> (result == (a & b))
    );

// ALU opcode 1001 selects bitwise AND.
    check_and_result_alt: assert property (
        @(posedge clk) (aluc == 4'b1001) |-> (result == (a & b))
    );

// ALU opcode 0101 selects bitwise OR.
    check_or_result: assert property (
        @(posedge clk) (aluc == 4'b0101) |-> (result == (a | b))
    );

// ALU opcode 1101 selects bitwise OR.
    check_or_result_alt: assert property (
        @(posedge clk) (aluc == 4'b1101) |-> (result == (a | b))
    );

// ALU opcode 1010 selects bitwise XOR.
    check_xor_result: assert property (
        @(posedge clk) (aluc == 4'b1010) |-> (result == (a ^ b))
    );

// ALU opcode 0010 selects bitwise XOR.
    check_xor_result_alt: assert property (
        @(posedge clk) (aluc == 4'b0010) |-> (result == (a ^ b))
    );

// ALU opcode 0110 selects zero-extended b.
    check_lui_result: assert property (
        @(posedge clk) (aluc == 4'b0110) |-> (result == {16'b0, b[15:0]})
    );

// ALU opcode 1110 selects zero-extended b.
    check_lui_result_alt: assert property (
        @(posedge clk) (aluc == 4'b1110) |-> (result == {16'b0, b[15:0]})
    );

// ALU opcode 0011 selects logical left shift by a.
    check_sll_result: assert property (
        @(posedge clk) (aluc == 4'b0011) |-> (result == (b << a))
    );

// ALU opcode 0111 selects logical right shift by a.
    check_srl_result: assert property (
        @(posedge clk) (aluc == 4'b0111) |-> (result == (b >> a))
    );

// ALU opcode 1111 selects arithmetic right shift by a.
    check_sra_result: assert property (
        @(posedge clk) (aluc == 4'b1111) |-> (result == ($signed(b) >>> a))
    );

// Default opcode 1111 selects addition.
    check_default_add_result: assert property (
        @(posedge clk) (aluc == 4'b1111) |-> (result == (a + b))
    );

endmodule
