module accumulator_assertions (
    input logic        clk,
    input logic [15:0] data,
    input logic [15:0] acc
);

    // Clock: clk
    // Reset: none
    // Sequential accumulator with registered output

    // The accumulator adds the previous cycle's data on each rising clock edge.
    check_accumulates_data: assert property (
        @(posedge clk) disable iff (1'b0)
        1'b1 |=> acc == ($past(acc) + $past(data))
    );

    // The cycle-to-cycle change in acc matches the previous cycle's data.
    check_cycle_delta_matches_data: assert property (
        @(posedge clk) disable iff (1'b0)
        1'b1 |=> (acc - $past(acc)) == $past(data)
    );

    // A zero input leaves the accumulator unchanged on the next cycle.
    check_hold_on_zero_data: assert property (
        @(posedge clk) disable iff (1'b0)
        data == 16'd0 |=> acc == $past(acc)
    );

    // An input of one increments the accumulator by one on the next cycle.
    check_increment_on_one: assert property (
        @(posedge clk) disable iff (1'b0)
        data == 16'd1 |=> acc == ($past(acc) + 16'd1)
    );

    // If the accumulator is zero, the next value equals the current input data.
    check_load_data_from_zero: assert property (
        @(posedge clk) disable iff (1'b0)
        acc == 16'd0 |=> acc == $past(data)
    );

    // Adding one to 16'hFFFF wraps the accumulator to zero.
    check_wrap_on_full_plus_one: assert property (
        @(posedge clk) disable iff (1'b0)
        (acc == 16'hFFFF) && (data == 16'd1) |=> acc == 16'd0
    );

    // An input of 16'hFFFF decrements the accumulator by one on the next cycle.
    check_decrement_on_all_ones_data: assert property (
        @(posedge clk) disable iff (1'b0)
        data == 16'hFFFF |=> acc == ($past(acc) - 16'd1)
    );

endmodule