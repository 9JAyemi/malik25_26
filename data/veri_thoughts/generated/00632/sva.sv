module top_module_sva (
    input logic clk,
    input logic [3:0] data_in,
    input logic load,
    input logic EN,
    input logic [7:0] final_output
);

    ///// Counter upper-nibble behavior (COUNT is held at reset) /////
    // Upper nibble is always 0 because binary_counter RST=0 holds COUNT at 0.
    check_upper_nibble_zero: assert property (
        @(posedge clk) disable iff (1'b0) $past(1'b1) |-> (final_output[7:4] == 4'b0000)
    );

    // Upper nibble never changes across cycles.
    check_upper_nibble_stable: assert property (
        @(posedge clk) disable iff (1'b0) $past(1'b1) |-> $stable(final_output[7:4])
    );

    ///// Shift-register lower-nibble behavior (via functional_module passthrough) /////
    // If load was 1 last cycle, lower nibble equals last cycle's data_in.
    load_captures_data: assert property (
        @(posedge clk) disable iff (1'b0) $past(1'b1) && $past(load) |-> (final_output[3:0] == $past(data_in))
    );

    // If load was 0 last cycle, lower nibble shifts left inserting 0 at LSB.
    shift_when_no_load: assert property (
        @(posedge clk) disable iff (1'b0) $past(1'b1) && !$past(load) |-> (final_output[3:0] == {$past(final_output[2:0]), 1'b0})
    );

    // If last cycle was a shift (no load), new LSB is 0.
    shift_lsb_zero: assert property (
        @(posedge clk) disable iff (1'b0) $past(1'b1) && !$past(load) |-> (final_output[0] == 1'b0)
    );

    // If last cycle was a shift (no load), bit1 moves into bit2.
    shift_moves_bit1_to_bit2: assert property (
        @(posedge clk) disable iff (1'b0) $past(1'b1) && !$past(load) |-> (final_output[2] == $past(final_output[1]))
    );

    // If last cycle was a shift (no load), bit2 moves into bit3.
    shift_moves_bit2_to_bit3: assert property (
        @(posedge clk) disable iff (1'b0) $past(1'b1) && !$past(load) |-> (final_output[3] == $past(final_output[2]))
    );

    // After 4 consecutive no-load cycles, the lower nibble must be 0.
    four_shifts_clear_lower: assert property (
        @(posedge clk) disable iff (1'b0)
            $past(1'b1,4) && !$past(load,3) && !$past(load,2) && !$past(load,1) && !load
            |-> (final_output[3:0] == 4'b0000)
    );

    // Load followed by one shift results in {data_in[2:0], 1'b0}.
    load_then_one_shift: assert property (
        @(posedge clk) disable iff (1'b0)
            $past(1'b1,1) && $past(load) && !load
            |-> (final_output[3:0] == {$past(data_in[2:0]), 1'b0})
    );

    // Load followed by two shifts results in {data_in[1:0], 2'b00}.
    load_then_two_shifts: assert property (
        @(posedge clk) disable iff (1'b0)
            $past(1'b1,2) && $past(load,2) && $past(!load,1) && !load
            |-> (final_output[3:0] == {$past(data_in[1:0],2), 2'b00})
    );

    // Load followed by three shifts results in {data_in[0], 3'b000}.
    load_then_three_shifts: assert property (
        @(posedge clk) disable iff (1'b0)
            $past(1'b1,3) && $past(load,3) && $past(!load,2) && $past(!load,1) && !load
            |-> (final_output[3:0] == {$past(data_in[0],3), 3'b000})
    );

endmodule