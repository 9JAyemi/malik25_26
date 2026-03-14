module RegisterAdd_sva #(
    parameter W = 16
) (
    input logic clk,
    input logic rst,
    input logic load,
    input logic [W-1:0] D,
    input logic [W-1:0] Q
);
    // Clock: clk; Reset: rst (active-high async)

    // Reset drives Q to zero whenever rst is HIGH.
    registeradd_check_reset_forces_zero: assert property (
        @(posedge clk) rst |-> (Q == '0)
    );

    // When not in reset (now and last cycle) and load is LOW, Q holds its value.
    registeradd_check_hold_when_not_load: assert property (
        @(posedge clk) disable iff (rst)
            (!$past(rst) && !load) |=> (Q == $past(Q))
    );

    // When not in reset (now and last cycle) and load is HIGH, Q updates to D.
    registeradd_check_load_captures_d: assert property (
        @(posedge clk) disable iff (rst)
            (!$past(rst) && load) |=> (Q == $past(D))
    );

    // Immediately after reset deasserts, if load is LOW, Q remains zero.
    registeradd_check_after_reset_no_load_q_zero: assert property (
        @(posedge clk) disable iff (rst)
            ($past(rst) && !load) |-> (Q == '0)
    );

    // Immediately after reset deasserts, if load is HIGH, next Q equals current D.
    registeradd_check_after_reset_with_load_captures_d: assert property (
        @(posedge clk) disable iff (rst)
            ($past(rst) && load) |=> (Q == $past(D))
    );

    // If load stayed LOW across two cycles with no reset, Q must be stable.
    registeradd_check_two_cycle_hold: assert property (
        @(posedge clk) disable iff (rst)
            (!$past(rst) && !load && !$past(load)) |-> (Q == $past(Q))
    );

endmodule


module FFD_NoCE_sva #(
    parameter W = 16
) (
    input logic clk,
    input logic rst,
    input logic [W-1:0] D,
    input logic [W-1:0] Q
);
    // Clock: clk; Reset: rst (active-high async)

    // Reset drives Q to zero whenever rst is HIGH.
    ffd_check_reset_forces_zero: assert property (
        @(posedge clk) rst |-> (Q == '0)
    );

    // With no reset in the previous cycle, Q equals prior D on this cycle.
    ffd_check_d_captured_no_reset: assert property (
        @(posedge clk) disable iff (rst)
            (!$past(rst)) |-> (Q == $past(D))
    );

    // On the first cycle after reset deasserts, next Q equals current D.
    ffd_check_after_reset_capture: assert property (
        @(posedge clk) disable iff (rst)
            ($past(rst)) |=> (Q == $past(D))
    );

    // While reset remains asserted across cycles, Q stays at zero.
    ffd_check_reset_holds_zero: assert property (
        @(posedge clk) (rst && $past(rst)) |-> (Q == '0)
    );

endmodule