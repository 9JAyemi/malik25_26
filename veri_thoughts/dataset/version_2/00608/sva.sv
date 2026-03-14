module clock_module_sva (
    input logic inclk0,
    input logic c0,
    input logic c1,
    input logic locked,
    input logic e0
);
    // c0 must equal inclk0.
    check_c0_eq_inclk0: assert property (
        @(posedge inclk0) c0 == inclk0
    );

    // c1 must equal inclk0.
    check_c1_eq_inclk0: assert property (
        @(posedge inclk0) c1 == inclk0
    );

    // e0 must be the inversion of inclk0.
    check_e0_inverts_inclk0: assert property (
        @(posedge inclk0) e0 == ~inclk0
    );

    // locked must be constantly HIGH.
    check_locked_constant_high: assert property (
        @(posedge inclk0) locked == 1'b1
    );

    // c0 and c1 must always be equal.
    check_c0_c1_equal: assert property (
        @(posedge inclk0) c0 == c1
    );

    // e0 must be the inversion of c0.
    check_e0_inverts_c0: assert property (
        @(posedge inclk0) e0 == ~c0
    );

    // On inclk0 posedge, outputs reflect expected phase: c0=1, c1=1, e0=0.
    check_posedge_phase_values: assert property (
        @(posedge inclk0) (c0 == 1'b1) && (c1 == 1'b1) && (e0 == 1'b0)
    );
endmodule