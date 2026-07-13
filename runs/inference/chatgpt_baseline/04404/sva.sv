module or3_2_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB,
    input logic X
);

    // X must equal the OR of the three pairwise AND terms.
    check_majority_function: assert property (
        @($global_clock) X == ((A & B) | (A & C) | (B & C))
    );

    // A and B high must drive X high.
    check_ab_pair_drives_x_high: assert property (
        @($global_clock) (A & B) |-> (X == 1'b1)
    );

    // A and C high must drive X high.
    check_ac_pair_drives_x_high: assert property (
        @($global_clock) (A & C) |-> (X == 1'b1)
    );

    // B and C high must drive X high.
    check_bc_pair_drives_x_high: assert property (
        @($global_clock) (B & C) |-> (X == 1'b1)
    );

    // With fewer than two inputs high, X must be low.
    check_fewer_than_two_high_drives_x_low: assert property (
        @($global_clock) !((A & B) | (A & C) | (B & C)) |-> (X == 1'b0)
    );

endmodule