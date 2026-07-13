module fpu_denorm_3to1_sva (
    input logic din2_din1_nz_hi,
    input logic din2_din1_denorm_hi,
    input logic din2_din1_nz_mid,
    input logic din2_din1_denorm_mid,
    input logic din2_din1_nz_lo,
    input logic din2_din1_denorm_lo,
    input logic din2_din1_nz,
    input logic din2_din1_denorm
);
    // NZ equals OR of hi/mid/lo NZ inputs.
    check_nz_definition_eq: assert property (
        @(posedge din2_din1_nz_hi or negedge din2_din1_nz_hi
        or posedge din2_din1_denorm_hi or negedge din2_din1_denorm_hi
        or posedge din2_din1_nz_mid or negedge din2_din1_nz_mid
        or posedge din2_din1_denorm_mid or negedge din2_din1_denorm_mid
        or posedge din2_din1_nz_lo or negedge din2_din1_nz_lo
        or posedge din2_din1_denorm_lo or negedge din2_din1_denorm_lo)
        din2_din1_nz == (din2_din1_nz_hi || din2_din1_nz_mid || din2_din1_nz_lo)
    );

    // HI NZ implies NZ.
    check_nz_hi_implies_nz: assert property (
        @(posedge din2_din1_nz_hi or negedge din2_din1_nz_hi
        or posedge din2_din1_denorm_hi or negedge din2_din1_denorm_hi
        or posedge din2_din1_nz_mid or negedge din2_din1_nz_mid
        or posedge din2_din1_denorm_mid or negedge din2_din1_denorm_mid
        or posedge din2_din1_nz_lo or negedge din2_din1_nz_lo
        or posedge din2_din1_denorm_lo or negedge din2_din1_denorm_lo)
        din2_din1_nz_hi |-> din2_din1_nz
    );

    // MID NZ implies NZ.
    check_nz_mid_implies_nz: assert property (
        @(posedge din2_din1_nz_hi or negedge din2_din1_nz_hi
        or posedge din2_din1_denorm_hi or negedge din2_din1_denorm_hi
        or posedge din2_din1_nz_mid or negedge din2_din1_nz_mid
        or posedge din2_din1_denorm_mid or negedge din2_din1_denorm_mid
        or posedge din2_din1_nz_lo or negedge din2_din1_nz_lo
        or posedge din2_din1_denorm_lo or negedge din2_din1_denorm_lo)
        din2_din1_nz_mid |-> din2_din1_nz
    );

    // LO NZ implies NZ.
    check_nz_lo_implies_nz: assert property (
        @(posedge din2_din1_nz_hi or negedge din2_din1_nz_hi
        or posedge din2_din1_denorm_hi or negedge din2_din1_denorm_hi
        or posedge din2_din1_nz_mid or negedge din2_din1_nz_mid
        or posedge din2_din1_denorm_mid or negedge din2_din1_denorm_mid
        or posedge din2_din1_nz_lo or negedge din2_din1_nz_lo
        or posedge din2_din1_denorm_lo or negedge din2_din1_denorm_lo)
        din2_din1_nz_lo |-> din2_din1_nz
    );

    // All NZ inputs low implies NZ low.
    check_nz_all_zero_implies_zero: assert property (
        @(posedge din2_din1_nz_hi or negedge din2_din1_nz_hi
        or posedge din2_din1_denorm_hi or negedge din2_din1_denorm_hi
        or posedge din2_din1_nz_mid or negedge din2_din1_nz_mid
        or posedge din2_din1_denorm_mid or negedge din2_din1_denorm_mid
        or posedge din2_din1_nz_lo or negedge din2_din1_nz_lo
        or posedge din2_din1_denorm_lo or negedge din2_din1_denorm_lo)
        (!din2_din1_nz_hi && !din2_din1_nz_mid && !din2_din1_nz_lo) |-> !din2_din1_nz
    );

    // DENORM equals priority-encoded combination of inputs.
    check_denorm_definition_eq: assert property (
        @(posedge din2_din1_nz_hi or negedge din2_din1_nz_hi
        or posedge din2_din1_denorm_hi or negedge din2_din1_denorm_hi
        or posedge din2_din1_nz_mid or negedge din2_din1_nz_mid
        or posedge din2_din1_denorm_mid or negedge din2_din1_denorm_mid
        or posedge din2_din1_nz_lo or negedge din2_din1_nz_lo
        or posedge din2_din1_denorm_lo or negedge din2_din1_denorm_lo)
        din2_din1_denorm ==
            ((din2_din1_nz_hi && din2_din1_denorm_hi)
            || ((!din2_din1_nz_hi) && din2_din1_nz_mid && din2_din1_denorm_mid)
            || ((!din2_din1_nz_hi) && (!din2_din1_nz_mid) && din2_din1_denorm_lo))
    );

    // When HI NZ is 1, DENORM equals DENORM_HI.
    check_denorm_depends_on_hi_when_hi_nz: assert property (
        @(posedge din2_din1_nz_hi or negedge din2_din1_nz_hi
        or posedge din2_din1_denorm_hi or negedge din2_din1_denorm_hi
        or posedge din2_din1_nz_mid or negedge din2_din1_nz_mid
        or posedge din2_din1_denorm_mid or negedge din2_din1_denorm_mid
        or posedge din2_din1_nz_lo or negedge din2_din1_nz_lo
        or posedge din2_din1_denorm_lo or negedge din2_din1_denorm_lo)
        din2_din1_nz_hi |-> (din2_din1_denorm == din2_din1_denorm_hi)
    );

    // When HI NZ is 0 and MID NZ is 1, DENORM equals DENORM_MID.
    check_denorm_depends_on_mid_when_mid_nz: assert property (
        @(posedge din2_din1_nz_hi or negedge din2_din1_nz_hi
        or posedge din2_din1_denorm_hi or negedge din2_din1_denorm_hi
        or posedge din2_din1_nz_mid or negedge din2_din1_nz_mid
        or posedge din2_din1_denorm_mid or negedge din2_din1_denorm_mid
        or posedge din2_din1_nz_lo or negedge din2_din1_nz_lo
        or posedge din2_din1_denorm_lo or negedge din2_din1_denorm_lo)
        (!din2_din1_nz_hi && din2_din1_nz_mid) |-> (din2_din1_denorm == din2_din1_denorm_mid)
    );

    // When HI and MID NZ are 0, DENORM equals DENORM_LO.
    check_denorm_depends_on_lo_when_hi_mid_zero: assert property (
        @(posedge din2_din1_nz_hi or negedge din2_din1_nz_hi
        or posedge din2_din1_denorm_hi or negedge din2_din1_denorm_hi
        or posedge din2_din1_nz_mid or negedge din2_din1_nz_mid
        or posedge din2_din1_denorm_mid or negedge din2_din1_denorm_mid
        or posedge din2_din1_nz_lo or negedge din2_din1_nz_lo
        or posedge din2_din1_denorm_lo or negedge din2_din1_denorm_lo)
        (!din2_din1_nz_hi && !din2_din1_nz_mid) |-> (din2_din1_denorm == din2_din1_denorm_lo)
    );

    // True HI path forces DENORM high.
    check_denorm_hi_path_true_sets_denorm: assert property (
        @(posedge din2_din1_nz_hi or negedge din2_din1_nz_hi
        or posedge din2_din1_denorm_hi or negedge din2_din1_denorm_hi
        or posedge din2_din1_nz_mid or negedge din2_din1_nz_mid
        or posedge din2_din1_denorm_mid or negedge din2_din1_denorm_mid
        or posedge din2_din1_nz_lo or negedge din2_din1_nz_lo
        or posedge din2_din1_denorm_lo or negedge din2_din1_denorm_lo)
        (din2_din1_nz_hi && din2_din1_denorm_hi) |-> din2_din1_denorm
    );

    // True MID path (with HI NZ=0) forces DENORM high.
    check_denorm_mid_path_true_sets_denorm: assert property (
        @(posedge din2_din1_nz_hi or negedge din2_din1_nz_hi
        or posedge din2_din1_denorm_hi or negedge din2_din1_denorm_hi
        or posedge din2_din1_nz_mid or negedge din2_din1_nz_mid
        or posedge din2_din1_denorm_mid or negedge din2_din1_denorm_mid
        or posedge din2_din1_nz_lo or negedge din2_din1_nz_lo
        or posedge din2_din1_denorm_lo or negedge din2_din1_denorm_lo)
        (!din2_din1_nz_hi && din2_din1_nz_mid && din2_din1_denorm_mid) |-> din2_din1_denorm
    );

    // True LO path (with HI and MID NZ=0) forces DENORM high.
    check_denorm_lo_path_true_sets_denorm: assert property (
        @(posedge din2_din1_nz_hi or negedge din2_din1_nz_hi
        or posedge din2_din1_denorm_hi or negedge din2_din1_denorm_hi
        or posedge din2_din1_nz_mid or negedge din2_din1_nz_mid
        or posedge din2_din1_denorm_mid or negedge din2_din1_denorm_mid
        or posedge din2_din1_nz_lo or negedge din2_din1_nz_lo
        or posedge din2_din1_denorm_lo or negedge din2_din1_denorm_lo)
        (!din2_din1_nz_hi && !din2_din1_nz_mid && din2_din1_denorm_lo) |-> din2_din1_denorm
    );

    // When HI NZ is 1 and DENORM_HI is 0, DENORM must be 0.
    check_denorm_hi_path_false_clears_denorm: assert property (
        @(posedge din2_din1_nz_hi or negedge din2_din1_nz_hi
        or posedge din2_din1_denorm_hi or negedge din2_din1_denorm_hi
        or posedge din2_din1_nz_mid or negedge din2_din1_nz_mid
        or posedge din2_din1_denorm_mid or negedge din2_din1_denorm_mid
        or posedge din2_din1_nz_lo or negedge din2_din1_nz_lo
        or posedge din2_din1_denorm_lo or negedge din2_din1_denorm_lo)
        (din2_din1_nz_hi && !din2_din1_denorm_hi) |-> !din2_din1_denorm
    );

    // When HI NZ=0 and MID NZ=1 with DENORM_MID=0, DENORM must be 0.
    check_denorm_mid_path_false_clears_denorm: assert property (
        @(posedge din2_din1_nz_hi or negedge din2_din1_nz_hi
        or posedge din2_din1_denorm_hi or negedge din2_din1_denorm_hi
        or posedge din2_din1_nz_mid or negedge din2_din1_nz_mid
        or posedge din2_din1_denorm_mid or negedge din2_din1_denorm_mid
        or posedge din2_din1_nz_lo or negedge din2_din1_nz_lo
        or posedge din2_din1_denorm_lo or negedge din2_din1_denorm_lo)
        (!din2_din1_nz_hi && din2_din1_nz_mid && !din2_din1_denorm_mid) |-> !din2_din1_denorm
    );

    // When HI and MID NZ=0 with DENORM_LO=0, DENORM must be 0.
    check_denorm_lo_path_false_clears_denorm: assert property (
        @(posedge din2_din1_nz_hi or negedge din2_din1_nz_hi
        or posedge din2_din1_denorm_hi or negedge din2_din1_denorm_hi
        or posedge din2_din1_nz_mid or negedge din2_din1_nz_mid
        or posedge din2_din1_denorm_mid or negedge din2_din1_denorm_mid
        or posedge din2_din1_nz_lo or negedge din2_din1_nz_lo
        or posedge din2_din1_denorm_lo or negedge din2_din1_denorm_lo)
        (!din2_din1_nz_hi && !din2_din1_nz_mid && !din2_din1_denorm_lo) |-> !din2_din1_denorm
    );
endmodule