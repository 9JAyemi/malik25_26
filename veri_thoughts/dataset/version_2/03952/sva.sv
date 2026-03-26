module counter_sva (
    input logic       CLK,
    input logic [3:0] Q
);

    // Q advances by one each cycle, wrapping from 15 to 0.
    check_counter_transition_relation: assert property (
        @(posedge CLK)
        1'b1 |=> (Q == (($past(Q) == 4'hf) ? 4'h0 : ($past(Q) + 4'h1)))
    );

    // A count of 15 wraps to 0 on the next clock.
    check_wrap_from_f_to_0: assert property (
        @(posedge CLK)
        (Q == 4'hf) |=> (Q == 4'h0)
    );

    // Any count below 15 increments by one on the next clock.
    check_increment_below_f: assert property (
        @(posedge CLK)
        (Q != 4'hf) |=> (Q == ($past(Q) + 4'h1))
    );

    // The counter never holds the same value on consecutive clocks.
    check_no_stall_between_cycles: assert property (
        @(posedge CLK)
        1'b1 |=> (Q != $past(Q))
    );

    // A value of 0 can only be reached from 15.
    check_zero_only_after_f: assert property (
        @(posedge CLK)
        1'b1 |=> ((Q != 4'h0) || ($past(Q) == 4'hf))
    );

    // A value of 15 can only be reached from 14.
    check_f_only_after_e: assert property (
        @(posedge CLK)
        1'b1 |=> ((Q != 4'hf) || ($past(Q) == 4'he))
    );

endmodule