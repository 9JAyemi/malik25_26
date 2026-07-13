module counter_sva (
    input logic       clk,
    input logic       rst,
    input logic       load,
    input logic [3:0] data_in,
    input logic [3:0] count_out
);

    // Active-low reset forces the counter output to zero.
    check_reset_clears_count: assert property (
        @(posedge clk) !rst |-> (count_out == 4'b0000)
    );

    // When load is high, the counter captures data_in on the next clock.
    check_load_captures_data: assert property (
        @(posedge clk) disable iff (!rst)
        load |=> (count_out == $past(data_in))
    );

    // When load is low, the counter increments by one on the next clock.
    check_increment_when_not_load: assert property (
        @(posedge clk) disable iff (!rst)
        !load |=> (count_out == ($past(count_out) + 4'b0001))
    );

    // The overall next-state behavior matches the RTL load-or-increment logic.
    check_next_state_function: assert property (
        @(posedge clk) disable iff (!rst)
        1'b1 |=> (count_out == ($past(load) ? $past(data_in) : ($past(count_out) + 4'b0001)))
    );

    // Incrementing from 4'hF wraps around to 4'h0.
    check_wraparound_from_max: assert property (
        @(posedge clk) disable iff (!rst)
        (!load && (count_out == 4'hF)) |=> (count_out == 4'h0)
    );

endmodule