module sync_resettable_latch_sva (
    input logic [3:0] D,
    input logic EN,
    input logic RST,
    input logic CLK,
    input logic [3:0] Q
);

    // Q follows the previous cycle's enabled load, reset, or hold behavior.
    check_q_follows_update_rule: assert property (
        @(posedge CLK) disable iff ($initstate)
        Q == ($past(EN) ? $past(D) : ($past(RST) ? 4'b0 : $past(Q)))
    );

    // Q captures D on the next clock when EN is high.
    check_q_loads_when_enabled: assert property (
        @(posedge CLK) disable iff ($initstate)
        EN |=> (Q == $past(D))
    );

    // Q clears on the next clock when RST is high and EN is low.
    check_q_clears_when_reset_without_enable: assert property (
        @(posedge CLK) disable iff ($initstate)
        (!EN && RST) |=> (Q == 4'b0)
    );

    // Q holds its value when neither EN nor RST is asserted.
    check_q_holds_when_idle: assert property (
        @(posedge CLK) disable iff ($initstate)
        (!EN && !RST) |=> (Q == $past(Q))
    );

    // EN has priority over RST when both are asserted.
    check_enable_has_priority_over_reset: assert property (
        @(posedge CLK) disable iff ($initstate)
        (EN && RST) |=> (Q == $past(D))
    );

endmodule