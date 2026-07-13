module alu_sva (
    input logic clk,
    input logic [3:0] a,
    input logic [3:0] b,
    input logic [2:0] op,
    input logic [3:0] out
);

// Addition opcode drives out to a + b.
    check_addition_result: assert property (
        @(posedge clk) (op == 3'b000) |-> (out == (a + b))
    );

// Subtraction opcode drives out to a - b.
    check_subtraction_result: assert property (
        @(posedge clk) (op == 3'b001) |-> (out == (a - b))
    );

// AND opcode drives out to a & b.
    check_and_result: assert property (
        @(posedge clk) (op == 3'b010) |-> (out == (a & b))
    );

// OR opcode drives out to a | b.
    check_or_result: assert property (
        @(posedge clk) (op == 3'b011) |-> (out == (a | b))
    );

// XOR opcode drives out to a ^ b.
    check_xor_result: assert property (
        @(posedge clk) (op == 3'b100) |-> (out == (a ^ b))
    );

// Shift-left opcode drives out to {a[2:0], 1'b0}.
    check_shift_left_result: assert property (
        @(posedge clk) (op == 3'b101) |-> (out == {a[2:0], 1'b0})
    );

// Default opcode drives out to 4'b0.
    check_default_zero: assert property (
        @(posedge clk) (op == 3'b110) |-> (out == 4'b0000)
    );

// Default opcode drives out to 4'b0.
    check_default_zero_111: assert property (
        @(posedge clk) (op == 3'b111) |-> (out == 4'b0000)
    );

endmodule
