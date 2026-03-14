module up_down_counter_sva (
    input logic [2:0] D,
    input logic UD,
    input logic LD,
    input logic CLK,
    input logic [2:0] Q
);

    // When LD=1, Q loads D on that clock.
    check_load_on_LD: assert property (
        @(posedge CLK) LD |-> (Q == D)
    );

    // When LD=0 and UD=1, Q decrements by 1 (mod-8).
    check_decrement_when_UD_no_LD: assert property (
        @(posedge CLK) (!LD && UD) |-> (Q == $past(Q) - 3'd1)
    );

    // When LD=0 and UD=0, Q increments by 1 (mod-8).
    check_increment_when_no_LD_no_UD: assert property (
        @(posedge CLK) (!LD && !UD) |-> (Q == $past(Q) + 3'd1)
    );

    // LD has priority over UD when both are 1.
    check_ld_overrides_ud: assert property (
        @(posedge CLK) (LD && UD) |-> (Q == D)
    );

    // With no load, the counter never holds its value.
    check_no_hold_when_no_LD: assert property (
        @(posedge CLK) (!LD) |-> (Q != $past(Q))
    );

    // Decrement wraps from 0 to 7.
    check_wrap_on_decrement_from_zero: assert property (
        @(posedge CLK) (!LD && UD && ($past(Q) == 3'd0)) |-> (Q == 3'd7)
    );

    // Increment wraps from 7 to 0.
    check_wrap_on_increment_from_seven: assert property (
        @(posedge CLK) (!LD && !UD && ($past(Q) == 3'd7)) |-> (Q == 3'd0)
    );

    // Two consecutive cycles of UD=1 and LD=0 subtract 2.
    check_two_cycle_decrement: assert property (
        @(posedge CLK) ((!LD && UD) ##1 (!LD && UD)) |-> (Q == $past(Q,2) - 3'd2)
    );

    // Two consecutive cycles of UD=0 and LD=0 add 2.
    check_two_cycle_increment: assert property (
        @(posedge CLK) ((!LD && !UD) ##1 (!LD && !UD)) |-> (Q == $past(Q,2) + 3'd2)
    );

endmodule