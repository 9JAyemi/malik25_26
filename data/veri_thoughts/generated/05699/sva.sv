module d_ff_sync_reset_set_ce_assertions (
    input logic CLK,
    input logic D,
    input logic RESET,
    input logic SET,
    input logic CE,
    input logic Q
);

    // Enabled updates follow RESET, then SET, then D priority.
    check_enabled_update_value: assert property (
        @(posedge CLK)
        CE |=> (Q == ($past(RESET) ? 1'b0 : ($past(SET) ? 1'b1 : $past(D))))
    );

    // RESET clears Q on the next clock when CE is high.
    check_reset_clears_q: assert property (
        @(posedge CLK)
        CE && RESET |=> (Q == 1'b0)
    );

    // RESET overrides SET when both are high and CE is high.
    check_reset_priority_over_set: assert property (
        @(posedge CLK)
        CE && RESET && SET |=> (Q == 1'b0)
    );

    // SET drives Q high when enabled and not in reset.
    check_set_sets_q: assert property (
        @(posedge CLK) disable iff (RESET)
        CE && SET |=> (Q == 1'b1)
    );

    // D is captured when enabled with neither RESET nor SET active.
    check_data_capture: assert property (
        @(posedge CLK) disable iff (RESET)
        CE && !SET |=> (Q == $past(D))
    );

    // Q holds its value whenever CE is low.
    check_ce_low_holds_q: assert property (
        @(posedge CLK)
        !CE |=> (Q == $past(Q))
    );

endmodule