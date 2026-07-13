module counter_sva (
    input logic       CLK,
    input logic       RST,
    input logic       UP_DOWN,
    input logic [3:0] Q
);

    // Synchronous reset loads Q with zero.
    check_reset_clears_q: assert property (
        @(posedge CLK) RST |=> (Q == 4'b0000)
    );

    // When counting up, Q increments by one.
    check_count_up_increments_q: assert property (
        @(posedge CLK) disable iff (RST)
        UP_DOWN |=> (Q == ($past(Q) + 4'b0001))
    );

    // When counting down, Q decrements by one.
    check_count_down_decrements_q: assert property (
        @(posedge CLK) disable iff (RST)
        !UP_DOWN |=> (Q == ($past(Q) - 4'b0001))
    );

    // Counting up wraps from 15 back to 0.
    check_count_up_wraps_to_zero: assert property (
        @(posedge CLK) disable iff (RST)
        (UP_DOWN && (Q == 4'b1111)) |=> (Q == 4'b0000)
    );

    // Counting down wraps from 0 back to 15.
    check_count_down_wraps_to_max: assert property (
        @(posedge CLK) disable iff (RST)
        (!UP_DOWN && (Q == 4'b0000)) |=> (Q == 4'b1111)
    );

endmodule