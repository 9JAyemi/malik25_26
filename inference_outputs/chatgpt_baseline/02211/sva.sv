module shift_right_sva (
    // DUT ports
    input logic        clk,
    input logic        rst,      // active-high asynchronous reset
    input logic        ld,
    input logic        shift,
    input logic [63:0] x,
    input logic        out,
    // Internal DUT signal (for bind)
    input logic [63:0] shiftreg
);
    // Clock: clk (posedge). Reset: rst (active-high async).
    // Behavior: load copies x into shiftreg and clears out; shift outputs LSB and shifts right with zero fill; rst clears state.

    ///// Reset behavior /////
    // If reset is sampled HIGH, next cycle shiftreg and out are zero.
    reset_clears_state: assert property (
        @(posedge clk) rst |=> (shiftreg == 64'd0) && (out == 1'b0)
    );

    // While reset is held across consecutive cycles, state is held at zero.
    reset_holds_zero: assert property (
        @(posedge clk) ($past(rst) && rst) |-> (shiftreg == 64'd0) && (out == 1'b0)
    );

    ///// Load behavior /////
    // Load clears out on the next cycle.
    load_clears_out: assert property (
        @(posedge clk) disable iff (rst) ld |=> (out == 1'b0)
    );

    // Load writes shiftreg with x on the next cycle (unless reset intervenes).
    load_writes_shiftreg: assert property (
        @(posedge clk) disable iff (rst) ld |=> (rst || (shiftreg == $past(x)))
    );

    ///// Shift behavior /////
    // On shift (without ld), next out equals prior LSB of shiftreg (unless reset intervenes).
    shift_moves_lsb_to_out: assert property (
        @(posedge clk) disable iff (rst) (shift && !ld) |=> (rst || (out == $past(shiftreg[0])))
    );

    // On shift (without ld), shiftreg shifts right with zero fill (unless reset intervenes).
    shift_updates_shiftreg: assert property (
        @(posedge clk) disable iff (rst) (shift && !ld) |=> (rst || (shiftreg == {1'b0, $past(shiftreg[63:1])}))
    );

    // On shift (without ld), MSB becomes 0 next cycle (unless reset intervenes).
    shift_msb_zero: assert property (
        @(posedge clk) disable iff (rst) (shift && !ld) |=> (rst || (shiftreg[63] == 1'b0))
    );

    // Shifting a zero register emits zero on out next cycle (unless reset intervenes).
    shift_zero_reg_out_zero: assert property (
        @(posedge clk) disable iff (rst) (shift && !ld && (shiftreg == 64'd0)) |=> (rst || (out == 1'b0))
    );

    ///// Priority /////
    // When ld and shift are both HIGH, out follows ld behavior (clears to 0).
    ld_priority_out: assert property (
        @(posedge clk) disable iff (rst) (ld && shift) |=> (rst || (out == 1'b0))
    );

    // When ld and shift are both HIGH, shiftreg follows ld behavior (loads x).
    ld_priority_shiftreg: assert property (
        @(posedge clk) disable iff (rst) (ld && shift) |=> (rst || (shiftreg == $past(x)))
    );

    ///// Progress under sustained shifting /////
    // After 64 consecutive shifts with no ld, the register becomes all zeros (or reset occurs).
    sequence s_64_shifts_no_ld;
        (shift && !ld)[*64];
    endsequence
    sixty_four_shifts_zero_reg: assert property (
        @(posedge clk) disable iff (rst) s_64_shifts_no_ld |=> (rst || (shiftreg == 64'd0))
    );

endmodule