module up_counter_sva (
    input logic clk,
    input logic reset,
    input logic load,
    input logic [3:0] data_in,
    input logic [3:0] data_out
);

    // After a reset cycle, the counter output is cleared.
    check_reset_clears_counter: assert property (
        @(posedge clk) disable iff ($initstate)
        ($past(reset)) |-> (data_out == 4'h0)
    );

    // A load cycle updates the counter with the input value.
    check_load_captures_data_in: assert property (
        @(posedge clk) disable iff ($initstate)
        (!$past(reset) && $past(load)) |-> (data_out == $past(data_in))
    );

    // Without reset or load, the counter increments by one.
    check_increment_when_idle: assert property (
        @(posedge clk) disable iff ($initstate)
        (!$past(reset) && !$past(load)) |-> (data_out == ($past(data_out) + 4'd1))
    );

    // Reset takes priority over load when both are asserted.
    check_reset_priority_over_load: assert property (
        @(posedge clk) disable iff ($initstate)
        ($past(reset) && $past(load)) |-> (data_out == 4'h0)
    );

    // The 4-bit counter wraps from 15 back to 0 on increment.
    check_wrap_from_f_to_0: assert property (
        @(posedge clk) disable iff ($initstate)
        (!$past(reset) && !$past(load) && ($past(data_out) == 4'hF)) |-> (data_out == 4'h0)
    );

endmodule