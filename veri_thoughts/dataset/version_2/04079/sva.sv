module zet_fulladd16_sva (
    input logic [15:0] x,
    input logic [15:0] y,
    input logic        ci,
    input logic        co,
    input logic [15:0] z,
    input logic        s
);

    // No RTL clock or reset; combinational behavior is sampled on $global_clock.

    // Combined carry-out and sum must match the implemented 17-bit addition.
    check_full_sum_match: assert property (
        @($global_clock) {co, z} == ({1'b0, x} + {s, y} + ci)
    );

    // With s low, the block behaves as x + y + ci.
    check_plain_add_when_s_low: assert property (
        @($global_clock) !s |-> {co, z} == ({1'b0, x} + {1'b0, y} + ci)
    );

    // With x and ci low, the output equals the s-extended y operand.
    check_y_pass_through_when_x_zero_and_ci_zero: assert property (
        @($global_clock) (x == 16'h0000 && !ci) |-> {co, z} == {s, y}
    );

    // With y and ci low, the output equals x with co matching s.
    check_x_pass_through_when_y_zero_and_ci_zero: assert property (
        @($global_clock) (y == 16'h0000 && !ci) |-> {co, z} == {s, x}
    );

    // Zero operands and no carry-in produce zero sum and co equal to s.
    check_zero_operands_no_carry_in: assert property (
        @($global_clock) (x == 16'h0000 && y == 16'h0000 && !ci) |-> (z == 16'h0000 && co == s)
    );

endmodule