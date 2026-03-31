module shift_register_sva (
    input logic clk,
    input logic shift_dir,
    input logic parallel_load,
    input logic [7:0] data_in,
    input logic [7:0] serial_out,
    input logic [7:0] parallel_out
);

    // parallel_out is the registered shift register value.
    check_parallel_out_registered: assert property (
        @(posedge clk) 1'b1 |=> (parallel_out == $past(parallel_out))
    );

    // serial_out is always the LSB of parallel_out.
    check_serial_out_matches_lsb: assert property (
        @(posedge clk) serial_out == parallel_out[0]
    );

    // parallel_load captures data_in into parallel_out.
    check_parallel_load_updates_register: assert property (
        @(posedge clk) parallel_load |=> (parallel_out == $past(data_in))
    );

    // parallel_load has priority over shift_dir.
    check_parallel_load_priority: assert property (
        @(posedge clk) (parallel_load && shift_dir) |=> (parallel_out == $past(data_in))
    );

    // shift_dir=1 rotates the register left and inserts 0 into bit 0.
    check_left_shift_update: assert property (
        @(posedge clk) (!parallel_load && shift_dir) |=> (parallel_out == { $past(parallel_out[6:0]), 1'b0 })
    );

    // shift_dir=0 rotates the register right and inserts 0 into bit 7.
    check_right_shift_update: assert property (
        @(posedge clk) (!parallel_load && !shift_dir) |=> (parallel_out == { 1'b0, $past(parallel_out[7:1]) })
    );

endmodule