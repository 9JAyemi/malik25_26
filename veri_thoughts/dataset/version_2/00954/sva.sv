module shift_register_8bit_sva (
    input logic clk,
    input logic load,
    input logic [7:0] data_in,
    input logic [7:0] data_out
);
    // Next-state equation: load -> data_in, else shift left with 0 LSB.
    check_next_state_equation: assert property (
        @(posedge clk) !$initstate |-> (data_out == ($past(load) ? $past(data_in) : { $past(data_out[6:0]), 1'b0 }))
    );

    // When load was 1, next data_out equals previous data_in.
    check_load_captures_input: assert property (
        @(posedge clk) (!$initstate && $past(load)) |-> (data_out == $past(data_in))
    );

    // When load was 0, next data_out equals left-shifted previous data_out with 0 inserted.
    check_shift_on_no_load: assert property (
        @(posedge clk) (!$initstate && !$past(load)) |-> (data_out == { $past(data_out[6:0]), 1'b0 })
    );

    // When load was 0, next LSB is 0.
    check_lsb_zero_on_shift: assert property (
        @(posedge clk) (!$initstate && !$past(load)) |-> (data_out[0] == 1'b0)
    );

    // When load was 0, upper 7 bits shift from previous lower 7 bits.
    check_upper_bits_shift_on_no_load: assert property (
        @(posedge clk) (!$initstate && !$past(load)) |-> (data_out[7:1] == $past(data_out[6:0]))
    );

    // After 8 consecutive no-load cycles, output becomes zero.
    check_zero_after_8_no_loads: assert property (
        @(posedge clk) (!load)[*8] |=> (data_out == 8'h00)
    );

    // After 2 consecutive no-load cycles, lower 2 bits are zero.
    check_lower2_zero_after_2_no_loads: assert property (
        @(posedge clk) (!load)[*2] |=> (data_out[1:0] == 2'b00)
    );

    // After 3 consecutive no-load cycles, lower 3 bits are zero.
    check_lower3_zero_after_3_no_loads: assert property (
        @(posedge clk) (!load)[*3] |=> (data_out[2:0] == 3'b000)
    );
endmodule