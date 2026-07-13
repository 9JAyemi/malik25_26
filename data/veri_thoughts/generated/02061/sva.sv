module lab5_1_1_sva (
    input logic clk,
    input logic reset,
    input logic ain,
    input logic [3:0] count,
    input logic yout,
    input logic [1:0] state,
    input logic [1:0] nextstate
);
    // Clock: clk (posedge). Reset: reset (active-high, synchronous).
    // Logic: mixed (seq: state/count; comb: nextstate/yout).
    // Behavior: count++ on ain; wrap at 15; state<=nextstate on ain; wrap forces state=S0; yout=1 only (S0 & !ain) or (S1 & ain) when !reset.

    localparam logic [1:0] S0 = 2'd0;
    localparam logic [1:0] S1 = 2'd1;
    localparam logic [1:0] S2 = 2'd2;
    localparam logic [1:0] S3 = 2'd3;

    ///// Reset behavior /////
    // On reset, count=0 and state=S0.
    check_reset_state_count: assert property (
        @(posedge clk) reset |-> (count == 4'd0) && (state == S0)
    );
    // On reset, yout is 0.
    check_reset_yout_low: assert property (
        @(posedge clk) reset |-> (yout == 1'b0)
    );

    ///// Hold behavior when ain=0 /////
    // With ain=0 (prev cycle), count holds.
    check_count_holds_when_ain_low: assert property (
        @(posedge clk) disable iff (reset) $past(!reset && !ain) |-> (count == $past(count))
    );
    // With ain=0 (prev cycle), state holds.
    check_state_holds_when_ain_low: assert property (
        @(posedge clk) disable iff (reset) $past(!reset && !ain) |-> (state == $past(state))
    );

    ///// Counter updates when ain=1 /////
    // With ain=1 (prev) and count!=15 (prev), count increments by 1.
    check_count_increments_on_ain_high: assert property (
        @(posedge clk) disable iff (reset) ($past(!reset && ain) && ($past(count) != 4'd15)) |-> (count == $past(count) + 4'd1)
    );
    // With ain=1 (prev) and count==15 (prev), count wraps to 0.
    check_count_wraps_on_max: assert property (
        @(posedge clk) disable iff (reset) ($past(!reset && ain) && ($past(count) == 4'd15)) |-> (count == 4'd0)
    );
    // Any count change (non-reset) implies ain was 1 in the previous cycle.
    check_count_change_requires_ain: assert property (
        @(posedge clk) disable iff (reset) (count != $past(count)) |-> $past(ain)
    );

    ///// State updates /////
    // With ain=1 (prev) and count!=15 (prev), state updates from previous nextstate.
    check_state_updates_from_nextstate: assert property (
        @(posedge clk) disable iff (reset) ($past(!reset && ain) && ($past(count) != 4'd15)) |-> (state == $past(nextstate))
    );
    // With ain=1 (prev) and count==15 (prev), state is forced to S0.
    check_state_S0_on_wrap: assert property (
        @(posedge clk) disable iff (reset) ($past(!reset && ain) && ($past(count) == 4'd15)) |-> (state == S0)
    );

    ///// nextstate combinational mapping /////
    // When in S0, nextstate = ain ? S2 : S0.
    check_nextstate_func_S0: assert property (
        @(posedge clk) disable iff (reset) (state == S0) |-> (nextstate == (ain ? S2 : S0))
    );
    // When in S1, nextstate = ain ? S2 : S1.
    check_nextstate_func_S1: assert property (
        @(posedge clk) disable iff (reset) (state == S1) |-> (nextstate == (ain ? S2 : S1))
    );
    // When in S2, nextstate = ain ? S3 : S2.
    check_nextstate_func_S2: assert property (
        @(posedge clk) disable iff (reset) (state == S2) |-> (nextstate == (ain ? S3 : S2))
    );
    // When in S3, nextstate = ain ? S1 : S3.
    check_nextstate_func_S3: assert property (
        @(posedge clk) disable iff (reset) (state == S3) |-> (nextstate == (ain ? S1 : S3))
    );

    ///// yout combinational truth table /////
    // When not in reset, yout == ((state==S0 && !ain) || (state==S1 && ain)).
    check_yout_truth_table: assert property (
        @(posedge clk) disable iff (reset) yout == (((state == S0) && !ain) || ((state == S1) && ain))
    );

endmodule