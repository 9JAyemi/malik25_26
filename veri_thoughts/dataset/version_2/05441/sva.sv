module up_down_counter_assertions (
    input logic CLK,
    input logic RST,
    input logic LD,
    input logic UD,
    input logic [3:0] LOAD_IN,
    input logic [3:0] Q
);

    // Synchronous reset clears Q on the next clock.
    check_reset_clears_q: assert property (
        @(posedge CLK) RST |=> (Q == 4'b0000)
    );

    // LD causes Q to take LOAD_IN on the next clock.
    check_load_updates_q: assert property (
        @(posedge CLK) disable iff (RST) LD |=> (Q == $past(LOAD_IN))
    );

    // LD has priority over UD when both are high.
    check_load_priority_over_ud: assert property (
        @(posedge CLK) disable iff (RST) (LD && UD) |=> (Q == $past(LOAD_IN))
    );

    // Without load, UD=1 increments Q by one.
    check_count_up: assert property (
        @(posedge CLK) disable iff (RST) (!LD && UD) |=> (Q == ($past(Q) + 4'b0001))
    );

    // Without load, UD=0 decrements Q by one.
    check_count_down: assert property (
        @(posedge CLK) disable iff (RST) (!LD && !UD) |=> (Q == ($past(Q) - 4'b0001))
    );

    // Incrementing from 4'hF wraps Q to 4'h0.
    check_count_up_wrap: assert property (
        @(posedge CLK) disable iff (RST) (!LD && UD && (Q == 4'hF)) |=> (Q == 4'h0)
    );

    // Decrementing from 4'h0 wraps Q to 4'hF.
    check_count_down_wrap: assert property (
        @(posedge CLK) disable iff (RST) (!LD && !UD && (Q == 4'h0)) |=> (Q == 4'hF)
    );

endmodule