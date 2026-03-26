module bit_shift_sva (
    input logic [31:0] in,
    input logic [4:0]  shift,
    input logic [1:0]  op,
    input logic [31:0] out
);

    // No DUT clock or reset; sample on the global clock.
    
    // op=00 selects a logical left shift.
    check_left_shift_result: assert property (
        @($global_clock) disable iff (1'b0)
        (op == 2'b00) |-> (out == (in << shift))
    );

    // op=01 selects a logical right shift.
    check_logical_right_shift_result: assert property (
        @($global_clock) disable iff (1'b0)
        (op == 2'b01) |-> (out == (in >> shift))
    );

    // op=10 selects an arithmetic right shift.
    check_arithmetic_right_shift_result: assert property (
        @($global_clock) disable iff (1'b0)
        (op == 2'b10) |-> (out == ($signed(in) >>> shift))
    );

    // op=11 follows the default passthrough behavior.
    check_default_passthrough_result: assert property (
        @($global_clock) disable iff (1'b0)
        (op == 2'b11) |-> (out == in)
    );

    // A zero shift amount leaves the value unchanged.
    check_zero_shift_passthrough: assert property (
        @($global_clock) disable iff (1'b0)
        (shift == 5'd0) |-> (out == in)
    );

    // Arithmetic right shift preserves the sign bit for nonzero shifts.
    check_arithmetic_shift_sign_preserved: assert property (
        @($global_clock) disable iff (1'b0)
        (op == 2'b10 && shift != 5'd0) |-> (out[31] == in[31])
    );

endmodule