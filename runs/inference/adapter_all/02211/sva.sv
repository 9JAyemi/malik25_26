module shift_right_sva (
    input logic        clk,
    input logic        rst,
    input logic        ld,
    input logic        shift,
    input logic [63:0] x,
    input logic        out,
    input logic [63:0] shiftreg
);

    // Reset clears the shift register and output.
    check_reset_clears_state: assert property (
        @(posedge clk) rst |-> ((shiftreg == 64'b0) && (out == 1'b0))
    );

    // Load captures x into the shift register and clears the output.
    check_load_captures_x: assert property (
        @(posedge clk) disable iff (rst) ld |-> ((shiftreg == x) && (out == 1'b0))
    );

    // Load has priority over shift when both are asserted.
    check_load_priority_over_shift: assert property (
        @(posedge clk) disable iff (rst) (ld && shift) |-> ((shiftreg == x) && (out == 1'b0))
    );

    // Shift moves the previous bit 0 into the output.
    check_shift_updates_output: assert property (
        @(posedge clk) disable iff (rst) (!ld && shift) |-> (out == shiftreg[0])
    );

    // Shift moves the previous bit 0 into the shift register.
    check_shift_updates_shiftreg: assert property (
        @(posedge clk) disable iff (rst) (!ld && shift) |-> (shiftreg == {1'b0, shiftreg[63:1]})
    );

    // With no load or shift, the shift register holds its value.
    check_hold_when_idle: assert property (
        @(posedge clk) disable iff (rst) (!ld && !shift) |-> (shiftreg == $past(shiftreg))
    );

    // With no load or shift, the output holds its value.
    check_hold_output_when_idle: assert property (
        @(posedge clk) disable iff (rst) (!ld && !shift) |-> (out == $past(out))
    );

endmodule