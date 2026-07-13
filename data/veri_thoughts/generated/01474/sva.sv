module multifsm_sva (
    input logic clk,
    input logic rst,
    input logic proddone,
    input logic start,
    input logic done,
    input logic ld,
    input logic shift,
    input logic [1:0] state,
    input logic [1:0] newstate
);
    // State encodings mirrored from RTL
    localparam logic [1:0] IDLE = 2'b00;
    localparam logic [1:0] MUL  = 2'b01;
    localparam logic [1:0] DONE = 2'b10;

    ///// Reset behavior /////
    // When reset is asserted, state must be IDLE.
    reset_state_idle: assert property (
        @(posedge clk) rst |-> (state == IDLE)
    );
    // When reset is asserted, outputs reflect IDLE (ld=1, done=0, shift=0).
    reset_outputs_idle: assert property (
        @(posedge clk) rst |-> (ld == 1'b1) && (done == 1'b0) && (shift == 1'b0)
    );

    ///// Sequential update /////
    // When not in reset, state updates from previous cycle's newstate.
    check_state_uses_newstate: assert property (
        @(posedge clk) disable iff (rst) state == $past(newstate)
    );

    ///// Next-state combinational logic /////
    // newstate calculation when in IDLE.
    nextstate_calc_idle: assert property (
        @(posedge clk) disable iff (rst) (state == IDLE) |-> (newstate == (start ? MUL : IDLE))
    );
    // newstate calculation when in MUL.
    nextstate_calc_mul: assert property (
        @(posedge clk) disable iff (rst) (state == MUL) |-> (newstate == ((start && proddone) ? DONE : (start ? MUL : IDLE)))
    );
    // newstate calculation when in DONE.
    nextstate_calc_done: assert property (
        @(posedge clk) disable iff (rst) (state == DONE) |-> (newstate == (start ? DONE : IDLE))
    );

    ///// Output decode /////
    // done is high iff state == DONE.
    check_done_decode: assert property (
        @(posedge clk) disable iff (rst) (done == (state == DONE))
    );
    // ld is high iff state == IDLE.
    check_ld_decode: assert property (
        @(posedge clk) disable iff (rst) (ld == (state == IDLE))
    );
    // shift is high iff state == MUL and proddone == 0.
    check_shift_decode: assert property (
        @(posedge clk) disable iff (rst) (shift == ((state == MUL) && !proddone))
    );
    // Shift equals (!done && !ld && !proddone).
    check_shift_vs_outputs: assert property (
        @(posedge clk) disable iff (rst) (shift == (!done && !ld && !proddone))
    );
    // ld and done are mutually exclusive.
    check_ld_done_mutex: assert property (
        @(posedge clk) disable iff (rst) !(ld && done)
    );

    ///// Temporal behavior from outputs /////
    // In DONE, next-cycle done equals current start.
    done_next_depends_on_start: assert property (
        @(posedge clk) disable iff (rst) done |-> ##1 (done == start)
    );
    // If ld and start==0, remain in IDLE next cycle (ld stays high).
    ld_holds_when_start_low: assert property (
        @(posedge clk) disable iff (rst) (ld && !start) |-> ##1 ld
    );
    // If ld and start==1, leave IDLE next cycle (ld goes low).
    ld_clears_when_start_high: assert property (
        @(posedge clk) disable iff (rst) (ld && start) |-> ##1 !ld
    );
    // From MUL with start && proddone, go to DONE next cycle.
    mul_to_done_on_start_and_proddone: assert property (
        @(posedge clk) disable iff (rst) (!ld && !done && start && proddone) |-> ##1 done
    );
    // From MUL with start && !proddone, stay in MUL next cycle.
    mul_stay_when_start_and_not_proddone: assert property (
        @(posedge clk) disable iff (rst) (!ld && !done && start && !proddone) |-> ##1 (!ld && !done)
    );
    // From MUL with !start, go to IDLE next cycle.
    mul_to_idle_when_start_low: assert property (
        @(posedge clk) disable iff (rst) (!ld && !done && !start) |-> ##1 ld
    );
    // A rising edge of done occurs only from MUL with start && proddone in the previous cycle.
    done_rise_from_mul_start_proddone: assert property (
        @(posedge clk) disable iff (rst) $rose(done) |-> ($past(!ld && !done) && $past(start) && $past(proddone))
    );
    // A falling edge of ld occurs only if start was high in the previous cycle.
    ld_fall_requires_start_high: assert property (
        @(posedge clk) disable iff (rst) $fell(ld) |-> $past(start)
    );
    // A rising edge of ld occurs only if start was low in the previous cycle.
    ld_rise_requires_start_low: assert property (
        @(posedge clk) disable iff (rst) $rose(ld) |-> !$past(start)
    );
    // A falling edge of done occurs only if start was low in the previous cycle.
    done_fall_requires_start_low: assert property (
        @(posedge clk) disable iff (rst) $fell(done) |-> !$past(start)
    );
endmodule