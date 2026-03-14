module d_ff_async_reset_set_sva (
    input logic clk,
    input logic d,
    input logic reset, // active-high synchronous reset
    input logic set,
    input logic q,
    input logic q_n
);
    // On reset, outputs go q=0, q_n=1.
    reset_forces_q0_qn1: assert property (
        @(posedge clk) reset |=> (q == 1'b0) && (q_n == 1'b1)
    );

    // With set high (and reset low), outputs q=1, q_n=0.
    set_forces_q1_qn0: assert property (
        @(posedge clk) disable iff (reset) set |=> (q == 1'b1) && (q_n == 1'b0)
    );

    // With no set, capture d and ~d from the previous cycle.
    data_captured_when_no_set: assert property (
        @(posedge clk) disable iff (reset) (!set) |=> (q == $past(d)) && (q_n == ~$past(d))
    );

    // Reset wins over set when both high.
    reset_over_set_priority: assert property (
        @(posedge clk) (reset && set) |=> (q == 1'b0) && (q_n == 1'b1)
    );

    // q_n is always ~q after update.
    complement_after_update: assert property (
        @(posedge clk) disable iff (reset) 1'b1 |=> (q_n == ~q)
    );

    // If no set and q==d, outputs hold.
    hold_when_q_equals_d: assert property (
        @(posedge clk) disable iff (reset) (!set && (q == d)) |=> ($stable(q) && $stable(q_n))
    );

    // If no set and d rises, q rises next.
    capture_d_rise: assert property (
        @(posedge clk) disable iff (reset) (!set && $rose(d)) |=> (q == 1'b1) && (q_n == 1'b0)
    );

    // If no set and d falls, q falls next.
    capture_d_fall: assert property (
        @(posedge clk) disable iff (reset) (!set && $fell(d)) |=> (q == 1'b0) && (q_n == 1'b1)
    );
endmodule