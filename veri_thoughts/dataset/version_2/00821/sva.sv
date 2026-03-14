module barrel_shift_up_down_counter_sva (
    input logic clk,
    input logic reset,
    input logic select,
    input logic [3:0] data_in,
    input logic [1:0] shift,
    input logic shift_right,
    input logic shift_left,
    input logic rotate_right,
    input logic rotate_left,
    input logic [3:0] count,
    input logic [3:0] shifted_data
);
    ///// Reset behavior /////
    // When reset is asserted, count and shifted_data are cleared to 0.
    check_reset_clears_regs: assert property (
        @(posedge clk) reset |-> (count == 4'b0000) && (shifted_data == 4'b0000)
    );

    ///// Count update /////
    // On each cycle out of reset, count updates to the previous shifted_data.
    check_count_follows_shifted_data: assert property (
        @(posedge clk) disable iff (reset) count == $past(shifted_data)
    );

    ///// Shift/rotate behavior for shifted_data /////
    // shift==2'b00 and shift_right: shifted_data <= {old[2:0], old[3]}.
    check_shift00_when_shift_right: assert property (
        @(posedge clk) disable iff (reset) (shift == 2'b00) && shift_right |-> shifted_data == { $past(shifted_data)[2:0], $past(shifted_data)[3] }
    );

    // shift==2'b00 and !shift_right: shifted_data <= {old[3], old[2:0]} (hold).
    check_shift00_when_not_shift_right: assert property (
        @(posedge clk) disable iff (reset) (shift == 2'b00) && !shift_right |-> shifted_data == { $past(shifted_data)[3], $past(shifted_data)[2:0] }
    );

    // shift==2'b01 and shift_left: shifted_data <= 4 LSBs of {old[3], old[2:0], old[1]} -> {old[2:0], old[1]}.
    check_shift01_when_shift_left: assert property (
        @(posedge clk) disable iff (reset) (shift == 2'b01) && shift_left |-> shifted_data == { $past(shifted_data)[2:0], $past(shifted_data)[1] }
    );

    // shift==2'b01 and !shift_left: shifted_data <= {old[0], old[3:1]}.
    check_shift01_when_not_shift_left: assert property (
        @(posedge clk) disable iff (reset) (shift == 2'b01) && !shift_left |-> shifted_data == { $past(shifted_data)[0], $past(shifted_data)[3:1] }
    );

    // shift==2'b10 and rotate_right: shifted_data <= {old[3], old[2:0]} (hold).
    check_shift10_when_rotate_right: assert property (
        @(posedge clk) disable iff (reset) (shift == 2'b10) && rotate_right |-> shifted_data == { $past(shifted_data)[3], $past(shifted_data)[2:0] }
    );

    // shift==2'b10 and !rotate_right: shifted_data <= {old[2], old[3:1]}.
    check_shift10_when_not_rotate_right: assert property (
        @(posedge clk) disable iff (reset) (shift == 2'b10) && !rotate_right |-> shifted_data == { $past(shifted_data)[2], $past(shifted_data)[3:1] }
    );

    // shift==2'b11 and rotate_left: shifted_data <= {old[3], old[0], old[2:1]}.
    check_shift11_when_rotate_left: assert property (
        @(posedge clk) disable iff (reset) (shift == 2'b11) && rotate_left |-> shifted_data == { $past(shifted_data)[3], $past(shifted_data)[0], $past(shifted_data)[2:1] }
    );

    // shift==2'b11 and !rotate_left: shifted_data <= 4 LSBs of {old[1], old[3:0]} -> old (hold).
    check_shift11_when_not_rotate_left: assert property (
        @(posedge clk) disable iff (reset) (shift == 2'b11) && !rotate_left |-> shifted_data == $past(shifted_data)
    );
endmodule