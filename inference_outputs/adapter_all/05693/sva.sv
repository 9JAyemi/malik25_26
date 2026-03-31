module shift_register_sva (
    input logic clk,
    input logic load,
    input logic [3:0] data_in,
    input logic [3:0] data_out
);

    // Load captures data_in into data_out on the next clock.
    check_load_captures_data: assert property (
        @(posedge clk) load |=> (data_out == $past(data_in))
    );

    // When not loading, data_out rotates left by one bit.
    check_rotate_when_not_loading: assert property (
        @(posedge clk) !load |=> (data_out == {$past(data_out[2:0]), $past(data_out[3])})
    );

    // The LSB takes the previous MSB when rotating.
    check_rotate_lsb_from_msb: assert property (
        @(posedge clk) !load |=> (data_out[0] == $past(data_out[3]))
    );

    // The next three bits take the previous three lower bits when rotating.
    check_rotate_upper_bits_from_lower: assert property (
        @(posedge clk) !load |=> (data_out[3:1] == $past(data_out[2:0]))
    );

    // Four consecutive rotates return data_out to its original value.
    check_four_rotate_cycle_identity: assert property (
        @(posedge clk) (!load)[*4] |=> (data_out == $past(data_out, 4))
    );

endmodule