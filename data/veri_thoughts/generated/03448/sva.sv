module my_module_sva (
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic C1
);

    // No RTL clock or reset; sample combinational behavior on the formal global clock.

    // Y must match the NOR of (B1&B2), C1, and (A1&A2).
    check_full_boolean_function: assert property (
        @($global_clock) Y == !((B1 & B2) | C1 | (A1 & A2))
    );

    // C1 high must force the NOR output low.
    check_c1_forces_low: assert property (
        @($global_clock) C1 |-> !Y
    );

    // A1 and A2 both high must force the NOR output low.
    check_a_pair_forces_low: assert property (
        @($global_clock) (A1 & A2) |-> !Y
    );

    // B1 and B2 both high must force the NOR output low.
    check_b_pair_forces_low: assert property (
        @($global_clock) (B1 & B2) |-> !Y
    );

    // If all NOR inputs are low, Y must be high.
    check_all_nor_inputs_low_drives_high: assert property (
        @($global_clock) (!C1 && !(A1 & A2) && !(B1 & B2)) |-> Y
    );

    // A high Y means every NOR input is low.
    check_high_output_means_all_nor_inputs_low: assert property (
        @($global_clock) Y |-> (!C1 && !(A1 & A2) && !(B1 & B2))
    );

endmodule