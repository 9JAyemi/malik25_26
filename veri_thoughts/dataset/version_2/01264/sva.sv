module counter_sva (
    input logic CLK,
    input logic CTRL,
    input logic LOAD,
    input logic [3:0] D,
    input logic [3:0] Q
);

    // Q next equals 0 if CTRL, else D if LOAD, else Q+1 (complete next-state function).
    check_next_state_function: assert property (
        @(posedge CLK)
            1'b1 |=> (
                ($past(CTRL) && (Q == 4'h0)) ||
                (!$past(CTRL) && $past(LOAD) && (Q == $past(D))) ||
                (!$past(CTRL) && !$past(LOAD) && (Q == $past(Q) + 4'd1))
            )
    );

    // When CTRL is high, Q becomes 0 on the next clock.
    check_ctrl_clears_q: assert property (
        @(posedge CLK) CTRL |=> (Q == 4'h0)
    );

    // CTRL has priority over LOAD when both are high.
    check_ctrl_over_load_priority: assert property (
        @(posedge CLK) (CTRL && LOAD) |=> (Q == 4'h0)
    );

    // When LOAD is high and CTRL is low, Q loads D on the next clock.
    check_load_without_ctrl_updates_q: assert property (
        @(posedge CLK) (!CTRL && LOAD) |=> (Q == $past(D))
    );

    // When neither CTRL nor LOAD are high, Q increments by 1 on the next clock.
    check_default_increment: assert property (
        @(posedge CLK) (!CTRL && !LOAD) |=> (Q == $past(Q) + 4'd1)
    );

    // Increment from 0xF wraps to 0x0 when neither CTRL nor LOAD are high.
    check_default_increment_wrap: assert property (
        @(posedge CLK) (!CTRL && !LOAD) |=> ( ($past(Q) == 4'hF) |-> (Q == 4'h0) )
    );

    // Under default increment case, Q changes value (no hold).
    check_default_increment_changes_value: assert property (
        @(posedge CLK) (!CTRL && !LOAD) |=> (Q != $past(Q))
    );

endmodule