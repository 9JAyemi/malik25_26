module dff_en_sva (
    input logic D,
    input logic C,
    input logic E,
    input logic Q
);
    // Q captures D on the next rising edge when E is HIGH.
    check_capture_when_enabled: assert property (
        @(posedge C) E |=> (Q == $past(D))
    );

    // Q holds its value on the next rising edge when E is LOW.
    check_hold_when_disabled: assert property (
        @(posedge C) !E |=> (Q == $past(Q))
    );

    // Any change in Q must be preceded by a rising edge of C.
    check_q_change_requires_clock: assert property (
        @(posedge C) $changed(Q) |-> $past(1'b1)
    );

    // If E is HIGH and D equals the current Q, Q must not change on the next rising edge.
    check_no_change_when_enabled_and_equal: assert property (
        @(posedge C) (E && (D == Q)) |=> (Q == $past(Q))
    );

    // If E is HIGH and D differs from the current Q, Q must change on the next rising edge.
    check_change_when_enabled_and_diff: assert property (
        @(posedge C) (E && (D != Q)) |=> (Q != $past(Q))
    );

    // If E is LOW and D differs from the current Q, Q must not change on the next rising edge.
    check_no_change_when_disabled_and_diff: assert property (
        @(posedge C) (!E && (D != Q)) |=> (Q == $past(Q))
    );

    // If E is LOW and D equals the current Q, Q must change on the next rising edge.
    check_change_when_disabled_and_equal: assert property (
        @(posedge C) (!E && (D == Q)) |=> (Q != $past(Q))
    );

    // If E is HIGH and D differs from the current Q, Q must equal D on the next rising edge.
    check_next_value_when_enabled_and_diff: assert property (
        @(posedge C) (E && (D != Q)) |=> (Q == $past(D))
    );

    // If E is LOW and D differs from the current Q, Q must equal the previous Q on the next rising edge.
    check_next_value_when_disabled_and_diff: assert property (
        @(posedge C) (!E && (D != Q)) |=> (Q == $past(Q))
    );

    // If E is HIGH and D equals the current Q, Q must equal D on the next rising edge.
    check_next_value_when_enabled_and_equal: assert property (
        @(posedge C) (E && (D == Q)) |=> (Q == $past(D))
    );
endmodule