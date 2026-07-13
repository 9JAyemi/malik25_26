module top_module_sva (
    input logic clk,
    input logic reset,
    input logic [3:0] load,
    input logic [3:0] compare,
    input logic [1:0] mode,
    input logic [3:0] count_out,
    input logic equal_out
);

    // Synchronous reset forces the counter output to zero by the next clock.
    check_reset_clears_counter: assert property (
        @(posedge clk)
        reset |=> (count_out == 4'h0)
    );

    // Mode 00 increments the counter by one.
    check_mode_increment: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        (mode == 2'b00) |=> (count_out == ($past(count_out) + 4'h1))
    );

    // Mode 01 decrements the counter by one.
    check_mode_decrement: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        (mode == 2'b01) |=> (count_out == ($past(count_out) - 4'h1))
    );

    // Mode 10 loads the input value into the counter.
    check_mode_load: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        (mode == 2'b10) |=> (count_out == $past(load))
    );

    // Mode 11 leaves the counter unchanged.
    check_mode_hold: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        (mode == 2'b11) |=> (count_out == $past(count_out))
    );

    // equal_out must assert when count_out matches compare.
    check_comparator_match: assert property (
        @(posedge clk) disable iff ($initstate)
        (count_out == compare) |-> equal_out
    );

    // equal_out must deassert when count_out differs from compare.
    check_comparator_mismatch: assert property (
        @(posedge clk) disable iff ($initstate)
        (count_out != compare) |-> !equal_out
    );

endmodule