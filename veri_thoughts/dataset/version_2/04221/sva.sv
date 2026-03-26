module up_down_counter_assertions (
    input logic clk,
    input logic up_down,
    input logic load,
    input logic reset,
    input logic [3:0] D,
    input logic [3:0] Q
);

    // Reset drives Q to zero on the following clock.
    check_reset_clears_q: assert property (
        @(posedge clk) disable iff ($initstate)
        reset |=> (Q == 4'b0000)
    );

    // Outside reset, Q follows the RTL next-state function.
    check_nonreset_next_state: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        1'b1 |=> (Q == ($past(load) ? $past(D) :
                       ($past(up_down) ? ($past(Q) + 4'd1) :
                                         ($past(Q) - 4'd1))))
    );

    // Load updates Q with D on the next clock.
    check_load_updates_q: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        load |=> (Q == $past(D))
    );

    // When load is low and up_down is high, Q increments by one.
    check_count_up_updates_q: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        (!load && up_down) |=> (Q == ($past(Q) + 4'd1))
    );

    // When load is low and up_down is low, Q decrements by one.
    check_count_down_updates_q: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        (!load && !up_down) |=> (Q == ($past(Q) - 4'd1))
    );

endmodule