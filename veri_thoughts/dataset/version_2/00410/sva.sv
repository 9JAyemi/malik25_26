module up_down_counter_sva (
    input logic clk,
    input logic load,
    input logic up_down,
    input logic [2:0] out
);

    // Counter state follows the RTL next-state function each cycle.
    check_next_state_matches_rtl: assert property (
        @(posedge clk)
        1'b1 |=> (out == ($past(load) ? 3'b000 :
                          ($past(up_down) ? ($past(out) + 3'b001) :
                                            ($past(out) - 3'b001))))
    );

    // A load request clears the counter to zero on the next cycle.
    check_load_clears_out: assert property (
        @(posedge clk)
        load |=> (out == 3'b000)
    );

    // With load low and up_down high, the counter increments by one.
    check_count_up: assert property (
        @(posedge clk)
        (!load && up_down) |=> (out == ($past(out) + 3'b001))
    );

    // With load low and up_down low, the counter decrements by one.
    check_count_down: assert property (
        @(posedge clk)
        (!load && !up_down) |=> (out == ($past(out) - 3'b001))
    );

    // Counting up wraps from 7 back to 0.
    check_count_up_wrap: assert property (
        @(posedge clk)
        (!load && up_down && (out == 3'b111)) |=> (out == 3'b000)
    );

    // Counting down wraps from 0 back to 7.
    check_count_down_wrap: assert property (
        @(posedge clk)
        (!load && !up_down && (out == 3'b000)) |=> (out == 3'b111)
    );

endmodule