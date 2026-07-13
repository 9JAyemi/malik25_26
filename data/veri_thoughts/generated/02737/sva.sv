module up_down_counter_sva (
    input logic clk,
    input logic UP,
    input logic DOWN,
    input logic LOAD,
    input logic [3:0] DIN,
    input logic [3:0] Q
);
    // Clock: clk (posedge). Reset: none.
    // Synchronous sequential counter with priority: LOAD > UP > DOWN.

    // When LOAD is high, Q loads DIN on the next cycle.
    check_load_updates_q: assert property (
        @(posedge clk) LOAD |=> (Q == $past(DIN))
    );

    // When LOAD=0 and UP=1, Q increments with wrap at 15.
    check_up_increments: assert property (
        @(posedge clk) (!LOAD && UP) |=> (Q == (($past(Q) == 4'hF) ? 4'h0 : ($past(Q) + 4'd1)))
    );

    // When LOAD=0, UP=0, and DOWN=1, Q decrements with wrap at 0.
    check_down_decrements: assert property (
        @(posedge clk) (!LOAD && !UP && DOWN) |=> (Q == (($past(Q) == 4'h0) ? 4'hF : ($past(Q) - 4'd1)))
    );

    // When LOAD=0 and UP=0 and DOWN=0, Q holds its value.
    check_hold_when_idle: assert property (
        @(posedge clk) (!LOAD && !UP && !DOWN) |=> (Q == $past(Q))
    );

    // When LOAD=0 and both UP and DOWN are 1, UP takes priority (count up).
    check_up_priority_over_down: assert property (
        @(posedge clk) (!LOAD && UP && DOWN) |=> (Q == (($past(Q) == 4'hF) ? 4'h0 : ($past(Q) + 4'd1)))
    );

    // Exact next-state function when LOAD=0 (encodes priority and wrap behavior).
    check_no_load_next_state_function: assert property (
        @(posedge clk) (!LOAD) |=> (
            Q == (
                $past(UP) ? (($past(Q) == 4'hF) ? 4'h0 : ($past(Q) + 4'd1)) :
                ($past(DOWN) ? (($past(Q) == 4'h0) ? 4'hF : ($past(Q) - 4'd1)) :
                $past(Q))
            )
        )
    );

endmodule