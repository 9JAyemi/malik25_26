module my_flip_flop_sva (
    input logic Q,
    input logic CLK,
    input logic D,
    input logic DE,
    input logic VPWR,
    input logic VGND
);
    // When DE was 1 on the previous edge, Q now equals previous D.
    check_capture_on_prev_enable: assert property (
        @(posedge CLK) $past(DE) |-> (Q == $past(D))
    );

    // When DE was 0 on the previous edge, Q holds its previous value.
    check_hold_on_prev_disable: assert property (
        @(posedge CLK) !$past(DE) |-> (Q == $past(Q))
    );

    // A change in Q since last edge implies DE was 1 on the previous edge.
    check_change_requires_prev_enable: assert property (
        @(posedge CLK) (Q != $past(Q)) |-> $past(DE)
    );

    // If DE was 1 and D differed from Q previously, Q must change.
    check_prev_enable_data_mismatch_causes_change: assert property (
        @(posedge CLK) ($past(DE) && ($past(D) != $past(Q))) |-> (Q != $past(Q))
    );

    // If DE was 1 and D matched Q previously, Q must not change.
    check_prev_enable_data_match_no_change: assert property (
        @(posedge CLK) ($past(DE) && ($past(D) == $past(Q))) |-> (Q == $past(Q))
    );

    // With DE=1 now, on the next edge Q equals the current D.
    check_capture_next_cycle_on_current_enable: assert property (
        @(posedge CLK) DE |-> ##1 (Q == $past(D))
    );

    // Q's update each cycle equals (DE ? D : hold) from the previous edge.
    check_functional_update_equation: assert property (
        @(posedge CLK) (Q == ($past(DE) ? $past(D) : $past(Q)))
    );
endmodule