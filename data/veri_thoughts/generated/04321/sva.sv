module sky130_fd_sc_hvl__lsbuflv2hv_isosrchvaon_sva (
    input logic X,
    input logic A,
    input logic SLEEP_B
);

    // On any port transition, the current stable state must satisfy X = A & SLEEP_B.
    check_x_matches_and_relation_on_port_activity: assert property (
        @(posedge A or negedge A or posedge SLEEP_B or negedge SLEEP_B or posedge X or negedge X)
        X == (A & SLEEP_B)
    );

    // Before A rises, X must already be low because A was low.
    check_x_low_before_a_rise: assert property (
        @(posedge A)
        X == 1'b0
    );

    // Before A falls, X must match SLEEP_B because A was high.
    check_x_matches_sleep_b_before_a_fall: assert property (
        @(negedge A)
        X == SLEEP_B
    );

    // Before SLEEP_B rises, X must already be low because sleep was active.
    check_x_low_before_sleep_b_rise: assert property (
        @(posedge SLEEP_B)
        X == 1'b0
    );

    // Before SLEEP_B falls, X must match A because the output was ungated.
    check_x_matches_a_before_sleep_b_fall: assert property (
        @(negedge SLEEP_B)
        X == A
    );

endmodule