module counter_assertions (
    input logic clk,
    input logic reset,
    input logic load,
    input logic [3:0] data_in,
    input logic [3:0] count_out,
    input logic wrap_around
);

    // Reset drives both outputs low by the next clock.
    check_reset_clears_outputs: assert property (
        @(posedge clk)
        reset |=> (count_out == 4'h0 && wrap_around == 1'b0)
    );

    // A load updates count_out from data_in and clears wrap_around.
    check_load_updates_count: assert property (
        @(posedge clk) disable iff (reset)
        load |=> (count_out == $past(data_in) && wrap_around == 1'b0)
    );

    // Without load, non-max values increment and keep wrap_around low.
    check_increment_when_not_max: assert property (
        @(posedge clk) disable iff (reset)
        (!load && (count_out != 4'hF)) |=> (count_out == ($past(count_out) + 4'h1) && wrap_around == 1'b0)
    );

    // Without load, 4'hF wraps to zero and asserts wrap_around.
    check_wrap_at_max: assert property (
        @(posedge clk) disable iff (reset)
        (!load && (count_out == 4'hF)) |=> (count_out == 4'h0 && wrap_around == 1'b1)
    );

endmodule