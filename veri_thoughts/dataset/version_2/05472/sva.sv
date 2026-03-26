module add_sub_shift_assertions (
    input logic clk,
    input logic [3:0] in0,
    input logic [3:0] in1,
    input logic SUB,
    input logic [1:0] SHIFT,
    input logic select,
    input logic [3:0] Y
);

    // No DUT clock or reset; assertions are sampled on external clk.

    // The top output must match the full add/sub, shift, and select behavior.
    check_top_function: assert property (
        @(posedge clk)
        Y == (
            select
                ? (SHIFT[1]
                    ? (((SUB ? (in0 - in1) : (in0 + in1)) >> SHIFT))
                    : (((SUB ? (in0 - in1) : (in0 + in1)) << SHIFT)))
                : (SUB ? (in0 - in1) : (in0 + in1))
        )
    );

    // When select is low and SUB is low, Y must be the 4-bit sum.
    check_bypass_add: assert property (
        @(posedge clk)
        (!select && !SUB) |-> (Y == (in0 + in1))
    );

    // When select is low and SUB is high, Y must be the 4-bit difference.
    check_bypass_sub: assert property (
        @(posedge clk)
        (!select && SUB) |-> (Y == (in0 - in1))
    );

    // When select is high and SHIFT[1] is low, Y must be the left-shifted add/sub result.
    check_selected_left_shift: assert property (
        @(posedge clk)
        (select && !SHIFT[1]) |-> (Y == ((SUB ? (in0 - in1) : (in0 + in1)) << SHIFT))
    );

    // When select is high and SHIFT[1] is high, Y must be the right-shifted add/sub result.
    check_selected_right_shift: assert property (
        @(posedge clk)
        (select && SHIFT[1]) |-> (Y == ((SUB ? (in0 - in1) : (in0 + in1)) >> SHIFT))
    );

    // A selected zero shift must leave the add/sub result unchanged.
    check_zero_shift_identity: assert property (
        @(posedge clk)
        (select && (SHIFT == 2'b00)) |-> (Y == (SUB ? (in0 - in1) : (in0 + in1)))
    );

    // If all inputs are stable, the combinational output must stay stable.
    check_stable_inputs_stable_output: assert property (
        @(posedge clk)
        $stable({in0, in1, SUB, SHIFT, select}) |-> $stable(Y)
    );

    // SHIFT changes must not affect Y while the unshifted path is selected.
    check_shift_ignored_when_bypassed: assert property (
        @(posedge clk)
        (!select && $stable({in0, in1, SUB, select}) && !$stable(SHIFT)) |-> $stable(Y)
    );

endmodule