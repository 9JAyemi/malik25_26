module aoi211hd4x_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic E,
    input logic F,
    input logic G,
    input logic H,
    input logic Z
);
    // No clock or reset in DUT; pure combinational AOI; sample on $global_clock.
    default clocking cb @($global_clock); endclocking

    // Z equals inversion of OR of four pairwise ANDs.
    check_functional_equivalence: assert property (
        Z == ~((A & B) | (C & D) | (E & F) | (G & H))
    );

    // AB high forces Z low.
    check_ab_forces_Z0: assert property (
        (A & B) |-> (Z == 1'b0)
    );

    // CD high forces Z low.
    check_cd_forces_Z0: assert property (
        (C & D) |-> (Z == 1'b0)
    );

    // EF high forces Z low.
    check_ef_forces_Z0: assert property (
        (E & F) |-> (Z == 1'b0)
    );

    // GH high forces Z low.
    check_gh_forces_Z0: assert property (
        (G & H) |-> (Z == 1'b0)
    );

    // No pair high implies Z high.
    check_no_pair_high_implies_Z1: assert property (
        (!(A & B) && !(C & D) && !(E & F) && !(G & H)) |-> (Z == 1'b1)
    );

    // Z high implies no pair high.
    check_Z1_implies_no_pair_high: assert property (
        (Z == 1'b1) |-> (!(A & B) && !(C & D) && !(E & F) && !(G & H))
    );

    // Z low implies at least one pair high.
    check_Z0_implies_some_pair_high: assert property (
        (Z == 1'b0) |-> ((A & B) || (C & D) || (E & F) || (G & H))
    );

    // If Z low and other pairs low, AB must be the cause.
    check_Z0_only_ab_causes_low: assert property (
        (Z == 1'b0) && !(C & D) && !(E & F) && !(G & H) |-> (A & B)
    );

    // If Z low and other pairs low, CD must be the cause.
    check_Z0_only_cd_causes_low: assert property (
        (Z == 1'b0) && !(A & B) && !(E & F) && !(G & H) |-> (C & D)
    );

    // If Z low and other pairs low, EF must be the cause.
    check_Z0_only_ef_causes_low: assert property (
        (Z == 1'b0) && !(A & B) && !(C & D) && !(G & H) |-> (E & F)
    );

    // If Z low and other pairs low, GH must be the cause.
    check_Z0_only_gh_causes_low: assert property (
        (Z == 1'b0) && !(A & B) && !(C & D) && !(E & F) |-> (G & H)
    );
endmodule