module shift_right_sva (
    input logic clk,
    input logic rst,
    input logic ld,
    input logic shift,
    input logic [63:0] x,
    input logic out,
    input logic [63:0] shiftreg
);

// Reset clears the shift register and output.
    check_reset_clears_state: assert property (
        @(posedge clk) rst |-> (shiftreg == 64'h0) && (out == 1'b0)
    );

// Load captures x into the shift register and clears the output.
    check_load_captures_x: assert property (
        @(posedge clk) disable iff (rst) ld |=> (shiftreg == $past(x)) && (out == 1'b0)
    );

// Shift moves the previous MSB into the output.
    check_shift_moves_msb_to_out: assert property (
        @(posedge clk) disable iff (rst) (!ld && shift) |=> (out == $past(shiftreg[0]))
    );

// Shift moves the previous register value left by one.
    check_shift_updates_register: assert property (
        @(posedge clk) disable iff (rst) (!ld && shift) |=> (shiftreg == {1'b0, $past(shiftreg[63:1])})
    );

// Shift has no effect when load is asserted.
    check_shift_overrides_load: assert property (
        @(posedge clk) disable iff (rst) (ld && shift) |=> (shiftreg == $past(x)) && (out == 1'b0)
    );

// Load has priority over shift when both are asserted.
    check_load_priority_over_shift: assert property (
        @(posedge clk) disable iff (rst) (ld && !shift) |=> (shiftreg == $past(x)) && (out == 1'b0)
    );

// With no control asserted, the register holds its value.
    check_hold_when_idle: assert property (
        @(posedge clk) disable iff (rst) (!ld && !shift) |=> (shiftreg == $past(shiftreg))
    );

// With no control asserted, the output holds its value.
    check_out_hold_when_idle: assert property (
        @(posedge clk) disable iff (rst) (!ld && !shift) |=> (out == $past(out))
    );

endmodule
