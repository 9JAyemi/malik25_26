module top_module_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic       sel,
    input logic [3:0] OUT
);

    // OUT matches the muxed twos complement of A and B.
    check_out_matches_muxed_twos_comp: assert property (
        @($global_clock) OUT == (sel ? (~A + 4'b0001) : B)
    );

    // When sel is low, OUT passes through B.
    check_sel_low_passes_b: assert property (
        @($global_clock) !sel |-> (OUT == B)
    );

    // When sel is high, OUT is the twos complement of A.
    check_sel_high_twos_comp_a: assert property (
        @($global_clock) sel |-> (OUT == (~A + 4'b0001))
    );

    // With sel low and B stable, OUT stays stable.
    check_b_stable_keeps_out_stable: assert property (
        @($global_clock) (!sel && $stable(B)) |-> $stable(OUT)
    );

    // With sel high and A stable, OUT stays stable.
    check_sel_high_a_stable_keeps_out_stable: assert property (
        @($global_clock) (sel && $stable(A)) |-> $stable(OUT)
    );

    // With sel low and B changing, OUT changes.
    check_b_change_updates_out: assert property (
        @($global_clock) (!sel && $changed(B)) |-> $changed(OUT)
    );

    // With sel high and A changing, OUT changes.
    check_sel_high_a_change_updates_out: assert property (
        @($global_clock) (sel && $changed(A)) |-> $changed(OUT)
    );

    // With sel low and B equal to the twos complement of A, OUT equals A.
    check_b_equals_twos_comp_a: assert property (
        @($global_clock) (!sel && (B == (~A + 4'b0001))) |-> (OUT == A)
    );

    // With sel high and A equal to B, OUT equals B.
    check_sel_high_a_equals_b: assert property (
        @($global_clock) (sel && (A == B)) |-> (OUT == B)
    );

    // With sel high and A equal to zero, OUT equals zero.
    check_sel_high_a_zero: assert property (
        @($global_clock) (sel && (A == 4'b0000)) |-> (OUT == 4'b0000)
    );

    // With sel high and A equal to 4'hF, OUT equals 4'h1.
    check_sel_high_a_all_ones: assert property (
        @($global_clock) (sel && (A == 4'h0F)) |-> (OUT == 4'h01)
    );

endmodule