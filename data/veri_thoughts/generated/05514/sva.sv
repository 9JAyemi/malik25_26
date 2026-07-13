module four_bit_alu_sva(
    input logic clk,
    input logic [3:0] ctl,
    input logic [3:0] a,
    input logic [3:0] b,
    input logic [3:0] out,
    input logic zero
);

    // Addition opcode drives out to a + b.
    check_addition_result: assert property (
        @(posedge clk) (ctl == 4'b0000) |-> (out == (a + b))
    );

    // Subtraction opcode drives out to a - b.
    check_subtraction_result: assert property (
        @(posedge clk) (ctl == 4'b0001) |-> (out == (a - b))
    );

    // AND opcode drives out to a & b.
    check_and_result: assert property (
        @(posedge clk) (ctl == 4'b0010) |-> (out == (a & b))
    );

    // OR opcode drives out to a | b.
    check_or_result: assert property (
        @(posedge clk) (ctl == 4'b0011) |-> (out == (a | b))
    );

    // XOR opcode drives out to a ^ b.
    check_xor_result: assert property (
        @(posedge clk) (ctl == 4'b0100) |-> (out == (a ^ b))
    );

    // NOT opcode drives out to ~a.
    check_not_result: assert property (
        @(posedge clk) (ctl == 4'b0101) |-> (out == (~a))
    );

    // Shift-left opcode drives out to a shifted left by one.
    check_shift_left_result: assert property (
        @(posedge clk) (ctl == 4'b0110) |-> (out == {a[2:0], 1'b0})
    );

    // Shift-right opcode drives out to a shifted right by one.
    check_shift_right_result: assert property (
        @(posedge clk) (ctl == 4'b0111) |-> (out == {1'b0, a[3:1]})
    );

    // Unused opcodes drive out to zero.
    check_default_result: assert property (
        @(posedge clk) ctl[3] |-> (out == 4'b0000)
    );

    // Zero flag matches whether out is all zeros.
    check_zero_flag: assert property (
        @(posedge clk) (zero == (out == 4'b0000))
    );

endmodule