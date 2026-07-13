module up_down_counter_sva (
    input logic CLK,
    input logic UP,
    input logic DOWN,
    input logic LD,
    input logic [2:0] DIN,
    input logic [2:0] Q
);

    // LD loads DIN on the next clock and overrides count controls.
    check_load_updates_q: assert property (
        @(posedge CLK) LD |=> (Q == $past(DIN))
    );

    // When not loading, UP increments Q on the next clock and has priority over DOWN.
    check_up_increments_q: assert property (
        @(posedge CLK) (!LD && UP) |=> (Q == ($past(Q) + 3'd1))
    );

    // DOWN decrements Q on the next clock only when LD and UP are both low.
    check_down_decrements_q: assert property (
        @(posedge CLK) (!LD && !UP && DOWN) |=> (Q == ($past(Q) - 3'd1))
    );

    // With no active control inputs, Q holds its value.
    check_hold_when_idle: assert property (
        @(posedge CLK) (!LD && !UP && !DOWN) |=> (Q == $past(Q))
    );

endmodule