module add_sub_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic       C,
    input logic [3:0] Q
);

    // When control is high, Q must be the 4-bit sum of A and B.
    check_add_mode_result: assert property (
        @($global_clock) (C == 1'b1) |-> (Q == (A + B))
    );

    // When control is low, Q must be the 4-bit difference of A and B.
    check_sub_mode_result: assert property (
        @($global_clock) (C == 1'b0) |-> (Q == (A - B))
    );

    // If all inputs are stable, the combinational output must remain stable.
    check_output_stable_when_inputs_stable: assert property (
        @($global_clock) $stable({A, B, C}) |-> $stable(Q)
    );

    // A rising control input selects the addition result.
    check_control_rise_selects_add: assert property (
        @($global_clock) $rose(C) |-> (Q == (A + B))
    );

    // A falling control input selects the subtraction result.
    check_control_fall_selects_sub: assert property (
        @($global_clock) $fell(C) |-> (Q == (A - B))
    );

endmodule