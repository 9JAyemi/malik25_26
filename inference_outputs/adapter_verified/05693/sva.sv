module shift_register_sva (
    input logic clk,
    input logic load,
    input logic [3:0] data_in,
    input logic [3:0] data_out
);

// Load captures data_in on the next cycle.
    check_load_captures_data: assert property (
        @(posedge clk) load |=> (data_out == $past(data_in))
    );

// When not loading, data_out rotates left by one bit.
    check_shift_left_when_not_loading: assert property (
        @(posedge clk) !load |=> (data_out == {$past(data_out[2:0]), $past(data_out[3])})
    );

// The least-significant bit takes the previous MSB value.
    check_lsb_captures_msb: assert property (
        @(posedge clk) !load |=> (data_out[0] == $past(data_out[3]))
    );

// The upper three bits shift left by one.
    check_upper_bits_shift_left: assert property (
        @(posedge clk) !load |=> (data_out[3:1] == $past(data_out[2:0]))
    );

endmodule
