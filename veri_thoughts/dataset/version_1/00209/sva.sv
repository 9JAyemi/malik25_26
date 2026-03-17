module top_module_assertions(
    input logic [99:0] in,
    input logic [3:0] in1,
    input logic [3:0] in2,
    input logic select,
    input logic out_and,
    input logic out_or,
    input logic out_xor
);

    // No RTL clock or reset; combinational checks are sampled on $global_clock.

    // out_and is the AND reduction of all 100 bits in in.
    check_out_and_function: assert property (
        @($global_clock) out_and == (&in)
    );

    // All input bits high forces out_and high.
    check_out_and_all_ones: assert property (
        @($global_clock) (&in) |-> (out_and == 1'b1)
    );

    // Any zero bit in in forces out_and low.
    check_out_and_not_all_ones: assert property (
        @($global_clock) !(&in) |-> (out_and == 1'b0)
    );

    // out_or is the OR reduction of the selected 4-bit result.
    check_out_or_function: assert property (
        @($global_clock) out_or == (|((select) ? (in1 & in2) : (in1 | in2)))
    );

    // select high chooses the bitwise-AND path for out_or.
    check_out_or_and_path: assert property (
        @($global_clock) (select == 1'b1) |-> (out_or == (|(in1 & in2)))
    );

    // select low chooses the bitwise-OR path for out_or.
    check_out_or_or_path: assert property (
        @($global_clock) (select == 1'b0) |-> (out_or == (|(in1 | in2)))
    );

    // On the AND path, a zero operand makes out_or low.
    check_out_or_and_zero_operand: assert property (
        @($global_clock) ((select == 1'b1) && ((in1 == 4'b0000) || (in2 == 4'b0000))) |-> (out_or == 1'b0)
    );

    // out_xor is the parity of the bitwise XOR of in1 and in2.
    check_out_xor_function: assert property (
        @($global_clock) out_xor == (^(in1 ^ in2))
    );

    // Equal operands make the XOR parity zero.
    check_out_xor_equal_inputs: assert property (
        @($global_clock) (in1 == in2) |-> (out_xor == 1'b0)
    );

    // With in2 at zero, out_xor matches the parity of in1.
    check_out_xor_zero_in2: assert property (
        @($global_clock) (in2 == 4'b0000) |-> (out_xor == (^in1))
    );

endmodule