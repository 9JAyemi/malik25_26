module nand4_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic Y,
    input logic VPB,
    input logic VPWR,
    input logic VGND,
    input logic VNB
);

    // Y matches the implemented NAND network.
    check_output_function: assert property (
        @($global_clock) Y == ~((A & B) | (C & D))
    );

    // A and B both high force Y low.
    check_ab_pair_forces_low: assert property (
        @($global_clock) (A & B) |-> ~Y
    );

    // C and D both high force Y low.
    check_cd_pair_forces_low: assert property (
        @($global_clock) (C & D) |-> ~Y
    );

    // A high Y means neither input pair is active.
    check_high_output_requires_no_active_pair: assert property (
        @($global_clock) Y |-> (~(A & B) & ~(C & D))
    );

    // A low Y means at least one input pair is active.
    check_low_output_requires_active_pair: assert property (
        @($global_clock) ~Y |-> ((A & B) | (C & D))
    );

    // With no active input pair, Y must be high.
    check_no_active_pair_drives_high: assert property (
        @($global_clock) (~(A & B) & ~(C & D)) |-> Y
    );

endmodule