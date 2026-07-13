module shift_register_sva (
    input logic       clk,
    input logic       load,
    input logic       shift_dir,
    input logic [7:0] parallel_in,
    input logic       serial_in,
    input logic [7:0] serial_out
);

    // Each cycle, serial_out follows the RTL next-state function.
    check_next_state_function: assert property (
        @(posedge clk)
        1'b1 |=> serial_out ==
                 ($past(load) ? $past(parallel_in) :
                  ($past(shift_dir) ? {$past(serial_in), $past(serial_out[7:1])} :
                                      {$past(serial_out[6:0]), $past(serial_in)}))
    );

    // When load is high, the register captures parallel_in on the next clock.
    check_load_captures_parallel_in: assert property (
        @(posedge clk)
        load |=> serial_out == $past(parallel_in)
    );

    // When not loading and shift_dir is high, the register shifts right.
    check_shift_right_updates_register: assert property (
        @(posedge clk)
        (!load && shift_dir) |=> serial_out == {$past(serial_in), $past(serial_out[7:1])}
    );

    // When not loading and shift_dir is low, the register shifts left.
    check_shift_left_updates_register: assert property (
        @(posedge clk)
        (!load && !shift_dir) |=> serial_out == {$past(serial_out[6:0]), $past(serial_in)}
    );

    // A right shift inserts serial_in into the MSB.
    check_shift_right_inserts_serial_in: assert property (
        @(posedge clk)
        (!load && shift_dir) |=> serial_out[7] == $past(serial_in)
    );

    // A right shift moves bits [7:1] into [6:0].
    check_shift_right_moves_data: assert property (
        @(posedge clk)
        (!load && shift_dir) |=> serial_out[6:0] == $past(serial_out[7:1])
    );

    // A left shift inserts serial_in into the LSB.
    check_shift_left_inserts_serial_in: assert property (
        @(posedge clk)
        (!load && !shift_dir) |=> serial_out[0] == $past(serial_in)
    );

    // A left shift moves bits [6:0] into [7:1].
    check_shift_left_moves_data: assert property (
        @(posedge clk)
        (!load && !shift_dir) |=> serial_out[7:1] == $past(serial_out[6:0])
    );

endmodule