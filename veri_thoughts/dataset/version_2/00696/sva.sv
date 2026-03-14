module adder_sva #(parameter WIDTH=8) (
    input logic clk,
    input logic rst,       // Active-high synchronous reset
    input logic load,
    input logic [WIDTH-1:0] A,
    input logic [WIDTH-1:0] B,
    input logic [WIDTH-1:0] Q
);

    ///// Reset behavior /////
    // One cycle after rst is asserted, Q must be zero.
    check_reset_clears_q_next: assert property (
        @(posedge clk) rst |=> (Q == '0)
    );

    // If rst is asserted in consecutive cycles, Q is zero in the later cycle.
    check_in_reset_q_zero_current: assert property (
        @(posedge clk) ($past(rst) && rst) |-> (Q == '0)
    );

    // Reset has priority over load; if both high, Q still clears to zero next cycle.
    check_reset_overrides_load: assert property (
        @(posedge clk) (rst && load) |=> (Q == '0)
    );

    ///// Sequential update semantics /////
    // Without load (and not coming from reset), Q holds its previous value.
    check_hold_without_load: assert property (
        @(posedge clk) disable iff (rst)
            ($past(1'b1) && !$past(load) && !$past(rst)) |-> (Q == $past(Q))
    );

    // Q only changes when the previous cycle had load or reset.
    check_change_requires_load_or_reset: assert property (
        @(posedge clk) disable iff (rst)
            ($past(1'b1) && (Q != $past(Q))) |-> ($past(load) || $past(rst))
    );

    ///// Functional correctness /////
    // After a load (and not from reset), Q equals A+B modulo WIDTH from the load cycle.
    check_sum_update_correct: assert property (
        @(posedge clk) disable iff (rst)
            ($past(1'b1) && $past(load) && !$past(rst)) |-> (Q == (($past(A) + $past(B)) [WIDTH-1:0]))
    );

    // LSB correctness after load: carry-in to bit 0 is 0, so Q[0] = A[0] ^ B[0].
    check_lsb_after_load: assert property (
        @(posedge clk) disable iff (rst)
            ($past(1'b1) && $past(load) && !$past(rst)) |-> (Q[0] == ($past(A[0]) ^ $past(B[0])))
    );

    // If load stays low for two consecutive cycles (no reset), Q remains constant across them.
    check_two_cycle_hold_no_load: assert property (
        @(posedge clk) disable iff (rst)
            ($past(1'b1) && !$past(load) && !load && !$past(rst)) |-> (Q == $past(Q))
    );

endmodule