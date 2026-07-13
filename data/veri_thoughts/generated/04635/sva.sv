module sky130_fd_sc_hd__o32ai_sva (
    input logic Y,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic B2
);

    // No RTL clock or reset; sample combinational behavior on the formal global clock.

    // Y must match the implemented OR-of-NOR logic.
    check_output_function: assert property (
        @($global_clock) Y == ((~(A3 | A1 | A2)) | (~(B1 | B2)))
    );

    // If all A inputs are low, Y must be high.
    check_a_group_clear_forces_high: assert property (
        @($global_clock) (!(A1 | A2 | A3)) |-> (Y == 1'b1)
    );

    // If all B inputs are low, Y must be high.
    check_b_group_clear_forces_high: assert property (
        @($global_clock) (!(B1 | B2)) |-> (Y == 1'b1)
    );

    // If at least one A input and one B input are high, Y must be low.
    check_both_groups_active_force_low: assert property (
        @($global_clock) ((A1 | A2 | A3) && (B1 | B2)) |-> (Y == 1'b0)
    );

    // A low Y requires both input groups to be active.
    check_low_output_requires_both_groups_active: assert property (
        @($global_clock) (Y == 1'b0) |-> ((A1 | A2 | A3) && (B1 | B2))
    );

    // A high Y requires either the A group or the B group to be all low.
    check_high_output_requires_clear_group: assert property (
        @($global_clock) (Y == 1'b1) |-> ((!(A1 | A2 | A3)) || (!(B1 | B2)))
    );

endmodule