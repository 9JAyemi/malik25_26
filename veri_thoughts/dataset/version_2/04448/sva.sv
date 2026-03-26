module alu_sva (
    input logic [3:0] a,
    input logic [3:0] b,
    input logic [2:0] op,
    input logic [3:0] out,
    input logic clk
);

    // Add opcode produces the delayed sum of the sampled operands.
    check_addition_result: assert property (
        @(posedge clk) disable iff (1'b0)
        (!$past($initstate,2) && ($past(op,2) == 3'b000))
        |-> (out == ($past(a,3) + $past(b,3)))
    );

    // Subtract opcode produces the delayed difference of the sampled operands.
    check_subtraction_result: assert property (
        @(posedge clk) disable iff (1'b0)
        (!$past($initstate,2) && ($past(op,2) == 3'b001))
        |-> (out == ($past(a,3) - $past(b,3)))
    );

    // AND opcode produces the delayed bitwise AND of the sampled operands.
    check_and_result: assert property (
        @(posedge clk) disable iff (1'b0)
        (!$past($initstate,2) && ($past(op,2) == 3'b010))
        |-> (out == ($past(a,3) & $past(b,3)))
    );

    // OR opcode produces the delayed bitwise OR of the sampled operands.
    check_or_result: assert property (
        @(posedge clk) disable iff (1'b0)
        (!$past($initstate,2) && ($past(op,2) == 3'b011))
        |-> (out == ($past(a,3) | $past(b,3)))
    );

    // XOR opcode produces the delayed bitwise XOR of the sampled operands.
    check_xor_result: assert property (
        @(posedge clk) disable iff (1'b0)
        (!$past($initstate,2) && ($past(op,2) == 3'b100))
        |-> (out == ($past(a,3) ^ $past(b,3)))
    );

    // Shift-left opcode produces the delayed left shift of the sampled A operand.
    check_shift_left_result: assert property (
        @(posedge clk) disable iff (1'b0)
        (!$past($initstate,2) && ($past(op,2) == 3'b101))
        |-> (out == { $past(a,3)[2:0], 1'b0 })
    );

    // Unsupported opcode 110 produces a delayed zero result.
    check_default_110_zero_result: assert property (
        @(posedge clk) disable iff (1'b0)
        (!$past($initstate,2) && ($past(op,2) == 3'b110))
        |-> (out == 4'b0000)
    );

    // Unsupported opcode 111 produces a delayed zero result.
    check_default_111_zero_result: assert property (
        @(posedge clk) disable iff (1'b0)
        (!$past($initstate,2) && ($past(op,2) == 3'b111))
        |-> (out == 4'b0000)
    );

endmodule