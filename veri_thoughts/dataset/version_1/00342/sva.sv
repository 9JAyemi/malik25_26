module shift_register_sva (
    input logic       clk,
    input logic       shift_dir,
    input logic       parallel_load,
    input logic [7:0] data_in,
    input logic [7:0] serial_out,
    input logic [7:0] parallel_out
);

    // serial_out is the zero-extended LSB of the register.
    check_serial_out_mapping: assert property (
        @(posedge clk) serial_out == {7'b0, parallel_out[0]}
    );

    // parallel_load loads data_in into the register on the next cycle.
    check_parallel_load_updates_register: assert property (
        @(posedge clk) parallel_load |=> parallel_out == $past(data_in)
    );

    // parallel_load also updates serial_out to the loaded bit 0 on the next cycle.
    check_parallel_load_updates_serial: assert property (
        @(posedge clk) parallel_load |=> serial_out == {7'b0, $past(data_in[0])}
    );

    // With no load, shift_dir=1 shifts the register left and inserts 0 in bit 0.
    check_left_shift_updates_register: assert property (
        @(posedge clk) (!parallel_load && shift_dir) |=> parallel_out == {$past(parallel_out[6:0]), 1'b0}
    );

    // A left shift forces serial_out to zero on the next cycle.
    check_left_shift_clears_serial_out: assert property (
        @(posedge clk) (!parallel_load && shift_dir) |=> serial_out == 8'h00
    );

    // With no load, shift_dir=0 shifts the register right and inserts 0 in bit 7.
    check_right_shift_updates_register: assert property (
        @(posedge clk) (!parallel_load && !shift_dir) |=> parallel_out == {1'b0, $past(parallel_out[7:1])}
    );

    // A right shift makes serial_out equal the prior bit 1 on the next cycle.
    check_right_shift_updates_serial: assert property (
        @(posedge clk) (!parallel_load && !shift_dir) |=> serial_out == {7'b0, $past(parallel_out[1])}
    );

endmodule