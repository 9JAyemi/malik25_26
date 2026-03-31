module shift_register_sva (
    input logic       clk,
    input logic       load,
    input logic [3:0] data_in,
    input logic [3:0] data_out
);

    // Load captures data_in into the register on the next cycle.
    check_load_captures_data: assert property (
        @(posedge clk) load |=> (data_out == $past(data_in))
    );

    // When not loading, the register shifts left and inserts zero at bit 0.
    check_shift_updates_register: assert property (
        @(posedge clk) !load |=> (data_out == {$past(data_out[2:0]), 1'b0})
    );

    // The upper three bits shift from the previous lower three bits.
    check_shift_moves_upper_bits: assert property (
        @(posedge clk) !load |=> (data_out[3:1] == $past(data_out[2:0]))
    );

    // Bit 0 is cleared whenever the register updates.
    check_shift_clears_bit0: assert property (
        @(posedge clk) 1'b1 |=> (data_out[0] == 1'b0)
    );

    // Four consecutive shifts return the register to its original value.
    check_four_shifts_return_to_original: assert property (
        @(posedge clk) (!load)[*4] |=> (data_out == $past(data_out, 4))
    );

endmodule