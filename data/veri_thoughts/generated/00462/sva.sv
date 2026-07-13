module binary_counter_sva (
    input logic       CLK,
    input logic       RST,
    input logic       COUNT_EN,
    input logic [3:0] Q
);

    // A reset cycle clears Q by the next sampled clock.
    check_reset_clears_q: assert property (
        @(posedge CLK) $past(RST) |-> (Q == 4'b0000)
    );

    // When enabled outside reset, Q increments by one.
    check_count_increment: assert property (
        @(posedge CLK) disable iff (RST)
        (!$past(RST) && $past(COUNT_EN)) |-> (Q == ($past(Q) + 4'd1))
    );

    // When not enabled outside reset, Q holds its value.
    check_hold_when_disabled: assert property (
        @(posedge CLK) disable iff (RST)
        (!$past(RST) && !$past(COUNT_EN)) |-> (Q == $past(Q))
    );

    // An enabled count wraps from 4'hF back to 4'h0.
    check_wrap_from_max: assert property (
        @(posedge CLK) disable iff (RST)
        (!$past(RST) && $past(COUNT_EN) && ($past(Q) == 4'hF)) |-> (Q == 4'h0)
    );

    // Q only changes after a reset cycle or an enabled count cycle.
    check_q_changes_only_after_action: assert property (
        @(posedge CLK) disable iff (RST)
        (Q != $past(Q)) |-> ($past(RST) || $past(COUNT_EN))
    );

endmodule