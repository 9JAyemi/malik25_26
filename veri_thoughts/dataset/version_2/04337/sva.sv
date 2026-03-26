module shift_register_sva (
    input logic clk,
    input logic parallel_load,
    input logic serial_in,
    input logic serial_out,
    input logic [3:0] data_in,
    input logic [3:0] pipeline [0:2]
);

    // serial_out mirrors the LSB of pipeline[2].
    check_serial_out_matches_pipeline2: assert property (
        @(posedge clk) serial_out == pipeline[2][0]
    );

    // pipeline[2] captures serial_in with zero extension on each clock.
    check_pipeline2_captures_serial_in: assert property (
        @(posedge clk) 1'b1 |=> pipeline[2] == {3'b000, $past(serial_in)}
    );

    // The upper bits of pipeline[2] are cleared after each update.
    check_pipeline2_upper_bits_zero: assert property (
        @(posedge clk) 1'b1 |=> pipeline[2][3:1] == 3'b000
    );

    // pipeline[1] captures the previous value of pipeline[2].
    check_pipeline1_captures_pipeline2: assert property (
        @(posedge clk) 1'b1 |=> pipeline[1] == $past(pipeline[2])
    );

    // pipeline[0] loads data_in when parallel_load is high.
    check_pipeline0_loads_data_in: assert property (
        @(posedge clk) parallel_load |=> pipeline[0] == $past(data_in)
    );

    // pipeline[0] shifts in pipeline[1] when parallel_load is low.
    check_pipeline0_shifts_pipeline1: assert property (
        @(posedge clk) !parallel_load |=> pipeline[0] == $past(pipeline[1])
    );

    // pipeline[0] always takes the selected source from the prior cycle.
    check_pipeline0_selected_source: assert property (
        @(posedge clk) 1'b1 |=> pipeline[0] == ($past(parallel_load) ? $past(data_in) : $past(pipeline[1]))
    );

    // serial_out reflects the serial_in value sampled on the prior clock.
    check_serial_out_tracks_serial_in: assert property (
        @(posedge clk) 1'b1 |=> serial_out == $past(serial_in)
    );

endmodule