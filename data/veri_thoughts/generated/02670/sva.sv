module DFFE_sva (
    input logic Q,
    input logic C,
    input logic E,
    input logic D
);
    // When enabled, next Q equals prior D.
    check_q_updates_on_enable: assert property (
        @(posedge C) E |=> (Q == $past(D))
    );

    // When disabled, next Q holds its previous value.
    check_q_holds_when_disabled: assert property (
        @(posedge C) !E |=> (Q == $past(Q))
    );

    // Any change in Q must be due to prior enable and equal prior D.
    check_q_change_requires_enable_and_matches_d: assert property (
        @(posedge C) $changed(Q) |-> ($past(E) && (Q == $past(D)))
    );

    // If enabled and D equals current Q, no change next cycle.
    check_no_change_when_enable_same_data: assert property (
        @(posedge C) (E && (D == Q)) |=> (Q == $past(Q))
    );

    // If enabled and D differs from current Q, Q must change next cycle.
    check_change_when_enable_diff_data: assert property (
        @(posedge C) (E && (D != Q)) |=> $changed(Q)
    );

    // Next Q equals mux of prior D and prior Q based on prior E.
    check_next_q_mux_of_e: assert property (
        @(posedge C) 1'b1 |=> (Q == ($past(E) ? $past(D) : $past(Q)))
    );
endmodule