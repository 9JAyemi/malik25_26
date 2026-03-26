module dff_2input_async_reset_set_sva (
    input logic clk,
    input logic reset,
    input logic set,
    input logic d,
    input logic q
);

    // Reset drives q low on the next clock.
    check_reset_forces_zero: assert property (
        @(posedge clk) disable iff ($initstate)
        reset |=> (q == 1'b0)
    );

    // Reset takes priority over set when both are high.
    check_reset_priority_over_set: assert property (
        @(posedge clk) disable iff ($initstate)
        (reset && set) |=> (q == 1'b0)
    );

    // Set drives q high when reset is low.
    check_set_forces_one: assert property (
        @(posedge clk) disable iff ($initstate || (reset && $past(reset)))
        (!reset && set) |=> (q == 1'b1)
    );

    // d=0 is captured when reset and set are low.
    check_data_zero_capture: assert property (
        @(posedge clk) disable iff ($initstate || (reset && $past(reset)))
        (!reset && !set && !d) |=> (q == 1'b0)
    );

    // d=1 is captured when reset and set are low.
    check_data_one_capture: assert property (
        @(posedge clk) disable iff ($initstate || (reset && $past(reset)))
        (!reset && !set && d) |=> (q == 1'b1)
    );

endmodule