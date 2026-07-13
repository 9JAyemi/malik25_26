module shift_register_sva (
    input logic clk,
    input logic [7:0] data,
    input logic [7:0] shifted_data
);

// Next cycle's shifted_data equals current data[6:0] concatenated with current data[7].
    check_shift_register_function: assert property (
        @(posedge clk) 1'b1 |=> (shifted_data == {$past(data[6:0]), $past(data[7])})
    );

// Upper 6 bits of shifted_data are the previous lower 6 bits.
    check_upper_bits_preserved: assert property (
        @(posedge clk) 1'b1 |=> (shifted_data[7:2] == $past(shifted_data[6:1]))
    );

// Lower bit of shifted_data is the previous MSB of data.
    check_lower_bit_from_msb: assert property (
        @(posedge clk) 1'b1 |=> (shifted_data[1] == $past(data[7]))
    );

// After 8 cycles, shifted_data equals the 8-cycle left rotation of the current input.
    check_8_cycle_rotation: assert property (
        @(posedge clk) 1'b1 |=> ##7 (shifted_data == {$past(data[7:1]), $past(data[0])})
    );

endmodule
