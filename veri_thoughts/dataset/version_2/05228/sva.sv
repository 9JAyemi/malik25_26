module shift_register_sva (
    input logic       clk,
    input logic [3:0] DIN,
    input logic       LOAD,
    input logic       SHIFT,
    input logic       RESET,
    input logic [3:0] Q
);

    // RESET clears Q to zero.
    check_reset_clears_q: assert property (
        @(posedge clk) RESET |=> (Q == 4'b0000)
    );

    // LOAD captures DIN when SHIFT is low.
    check_load_captures_din: assert property (
        @(posedge clk) disable iff (RESET)
        (LOAD && !SHIFT) |=> (Q == $past(DIN))
    );

    // LOAD has priority over SHIFT when both are high.
    check_load_priority_over_shift: assert property (
        @(posedge clk) disable iff (RESET)
        (LOAD && SHIFT) |=> (Q == $past(DIN))
    );

    // SHIFT moves Q left and inserts zero when LOAD is low.
    check_shift_updates_q: assert property (
        @(posedge clk) disable iff (RESET)
        (!LOAD && SHIFT) |=> (
            (Q[3] == $past(Q[2])) &&
            (Q[2] == $past(Q[1])) &&
            (Q[1] == $past(Q[0])) &&
            (Q[0] == 1'b0)
        )
    );

    // Q holds its value when no control is asserted.
    check_hold_when_idle: assert property (
        @(posedge clk) disable iff (RESET)
        (!LOAD && !SHIFT) |=> (Q == $past(Q))
    );

endmodule