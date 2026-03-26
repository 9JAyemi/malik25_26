module shift_register_sva (
    input logic clk,
    input logic reset,
    input logic load,
    input logic shift,
    input logic [7:0] data_in,
    input logic [7:0] parallel_in,
    input logic [7:0] data_out
);

    // Reset clears the register by the next clock.
    check_reset_clears_register: assert property (
        @(posedge clk) reset |=> (data_out == 8'h00)
    );

    // Load captures parallel_in when shift is low.
    check_load_captures_parallel_in: assert property (
        @(posedge clk) disable iff (reset)
        (load && !shift) |=> (data_out == $past(parallel_in))
    );

    // Load has priority over shift when both are high.
    check_load_priority_over_shift: assert property (
        @(posedge clk) disable iff (reset)
        (load && shift) |=> (data_out == $past(parallel_in))
    );

    // Shift moves data left and inserts 0 into bit 0.
    check_shift_left_zero_fill: assert property (
        @(posedge clk) disable iff (reset)
        (!load && shift) |=> (data_out == {$past(data_out[6:0]), 1'b0})
    );

    // Without load or shift, data_in is captured.
    check_default_captures_data_in: assert property (
        @(posedge clk) disable iff (reset)
        (!load && !shift) |=> (data_out == $past(data_in))
    );

endmodule