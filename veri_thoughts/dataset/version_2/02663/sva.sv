module shift_register_sva (
    input logic clk,
    input logic [3:0] IN,
    input logic PL,
    input logic SL,
    input logic SR,
    input logic [3:0] q
);
    // On PL, next q equals IN (highest priority).
    check_parallel_load: assert property (
        @(posedge clk) disable iff ($initstate)
            $past(PL) |-> (q == $past(IN))
    );

    // On SL without PL, next q is rotate-left by 1.
    check_shift_left_rotate: assert property (
        @(posedge clk) disable iff ($initstate)
            (!$past(PL) && $past(SL)) |-> (q == { $past(q[2:0]), $past(q[3]) })
    );

    // On SR without PL or SL, next q is rotate-right by 1.
    check_shift_right_rotate: assert property (
        @(posedge clk) disable iff ($initstate)
            (!$past(PL) && !$past(SL) && $past(SR)) |-> (q == { $past(q[0]), $past(q[3:1]) })
    );

    // With no control asserted, q holds its previous value.
    check_hold_when_idle: assert property (
        @(posedge clk) disable iff ($initstate)
            (!$past(PL) && !$past(SL) && !$past(SR)) |-> (q == $past(q))
    );

    // q changes only if at least one control was asserted.
    check_q_change_requires_enable: assert property (
        @(posedge clk) disable iff ($initstate)
            $changed(q) |-> $past(PL || SL || SR)
    );
endmodule