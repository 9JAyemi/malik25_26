module shift_right_sva (
    input logic clk,
    input logic rst,
    input logic ld,
    input logic shift,
    input logic [63:0] x,
    input logic out,
    input logic [63:0] shiftreg
);

    // Reset clears the shift register and forces out low.
    check_reset_clears_state: assert property (
        @(posedge clk)
        rst |-> ((shiftreg == 64'h0000000000000000) && (out == 1'b0))
    );

    // Load updates the shift register with x and clears out.
    check_load_updates_shiftreg: assert property (
        @(posedge clk) disable iff (rst)
        ld |=> ((shiftreg == $past(x)) && (out == 1'b0))
    );

    // Load has priority over shift when both are asserted.
    check_load_priority_over_shift: assert property (
        @(posedge clk) disable iff (rst)
        (ld && shift) |=> ((shiftreg == $past(x)) && (out == 1'b0))
    );

    // Shift moves the previous bit-0 into out and rotates the register right.
    check_shift_updates_state: assert property (
        @(posedge clk) disable iff (rst)
        (!ld && shift) |=> ((out == $past(shiftreg[0])) &&
                            (shiftreg == {1'b0, $past(shiftreg[63:1])}))
    );

    // Without load or shift, the state holds its value.
    check_idle_holds_state: assert property (
        @(posedge clk) disable iff (rst)
        (!ld && !shift) |=> ((shiftreg == $past(shiftreg)) && (out == $past(out)))
    );

endmodule