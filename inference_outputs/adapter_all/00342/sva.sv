module shift_register_sva (
    input logic clk,
    input logic shift_dir,
    input logic parallel_load,
    input logic [7:0] data_in,
    input logic [7:0] serial_out,
    input logic [7:0] parallel_out
);

    // parallel_out reflects the previous cycle's load or shift result.
    check_parallel_out_update: assert property (
        @(posedge clk)
        1'b1 |=> (parallel_out == ($past(parallel_load) ? $past(data_in) :
                   ($past(shift_dir) ? { $past(parallel_out[6:0]), 1'b0 } :
                                        { 1'b0, $past(parallel_out[7:1]) })))
    );

    // serial_out is the LSB of the previous cycle's parallel_out.
    check_serial_out_from_prev_parallel: assert property (
        @(posedge clk)
        1'b1 |=> (serial_out == $past(parallel_out[0]))
    );

    // parallel_load causes parallel_out to capture data_in on the next cycle.
    check_parallel_load_captures_data: assert property (
        @(posedge clk)
        parallel_load |=> (parallel_out == $past(data_in))
    );

    // parallel_load causes serial_out to reflect the loaded data LSB on the next cycle.
    check_serial_load_captures_data: assert property (
        @(posedge clk)
        parallel_load |=> (serial_out == $past(data_in[0]))
    );

    // shift_dir=1 causes parallel_out to shift left and insert 0 on the next cycle.
    check_shift_left_updates_parallel: assert property (
        @(posedge clk)
        (!parallel_load && shift_dir) |=> (parallel_out == { $past(parallel_out[6:0]), 1'b0 })
    );

    // shift_dir=0 causes parallel_out to shift right and insert 0 on the next cycle.
    check_shift_right_updates_parallel: assert property (
        @(posedge clk)
        (!parallel_load && !shift_dir) |=> (parallel_out == { 1'b0, $past(parallel_out[7:1]) })
    );

    // serial_out is always the LSB of parallel_out.
    check_serial_out_matches_parallel_lsb: assert property (
        @(posedge clk)
        (serial_out == parallel_out[0])
    );

    // A left shift followed by a right shift restores parallel_out to its original value.
    check_left_then_right_restores_parallel: assert property (
        @(posedge clk)
        (!parallel_load && shift_dir ##1 (!parallel_load && !shift_dir)) |=> (parallel_out == $past(parallel_out, 2))
    );

    // A right shift followed by a left shift restores parallel_out to its original value.
    check_right_then_left_restores_parallel: assert property (
        @(posedge clk)
        (!parallel_load && !shift_dir ##1 (!parallel_load && shift_dir)) |=> (parallel_out == $past(parallel_out, 2))
    );

endmodule