module shift_left_register_sva (
    input logic clk,
    input logic reset,
    input logic parallel_load,
    input logic shift,
    input logic [3:0] input_data,
    input logic [3:0] output_data
);

    // Reset drives the register output to zero.
    check_reset_clears_output: assert property (
        @(posedge clk) reset |=> (output_data == 4'b0000)
    );

    // Parallel load captures input_data on the next clock.
    check_parallel_load: assert property (
        @(posedge clk) disable iff (reset)
        parallel_load |=> (output_data == $past(input_data))
    );

    // Shift moves the stored value left and inserts zero in the LSB.
    check_shift_left: assert property (
        @(posedge clk) disable iff (reset)
        (shift && !parallel_load) |=> (output_data == {$past(output_data[2:0]), 1'b0})
    );

    // Parallel load has priority over shift when both are asserted.
    check_load_priority: assert property (
        @(posedge clk) disable iff (reset)
        (parallel_load && shift) |=> (output_data == $past(input_data))
    );

    // The register holds its value when neither control is asserted.
    check_hold_when_idle: assert property (
        @(posedge clk) disable iff (reset)
        (!parallel_load && !shift) |=> (output_data == $past(output_data))
    );

endmodule