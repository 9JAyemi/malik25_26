module register_4bit_sva (
    input logic [3:0] data_in,
    input logic load,
    input logic reset,   // active-high async reset in RTL
    input logic clk,
    input logic [3:0] Q
);

    // After a sampled reset, Q must be 0 on the next clock.
    check_reset_clears_next: assert property (
        @(posedge clk) disable iff (reset) $past(reset) |-> (Q == 4'b0000)
    );

    // With load high (reset low), Q updates to data_in on the next clock.
    check_load_captures_next: assert property (
        @(posedge clk) disable iff (reset) load |=> (Q == $past(data_in))
    );

    // After a sampled reset, if no load in the following cycle, Q remains 0 for one more cycle.
    check_zero_persists_one_more_cycle_without_load_after_reset: assert property (
        @(posedge clk) disable iff (reset) $past(reset) && !load |=> (Q == 4'b0000)
    );

    // Back-to-back loads pipeline data: second cycle reflects data_in of the first next cycle.
    check_back_to_back_loads_pipeline: assert property (
        @(posedge clk) disable iff (reset) load ##1 load |=> (Q == $past(data_in))
    );

    // If previous cycle had reset and current load is high, Q is 0 in the current cycle (reset dominates).
    check_reset_dominates_load_current: assert property (
        @(posedge clk) disable iff (reset) $past(reset) && load |-> (Q == 4'b0000)
    );

    // If previous cycle had reset and current load is high, Q captures current data on the next clock.
    check_reset_then_load_captures_next: assert property (
        @(posedge clk) disable iff (reset) $past(reset) && load |=> (Q == $past(data_in))
    );

endmodule