module dff_pn0_assertions (
    input logic D,
    input logic C,
    input logic R,
    input logic S,
    input logic Q
);

    // Active-low synchronous reset clears Q.
    check_reset_clears_q: assert property (
        @(posedge C) !R |=> (Q == 1'b0)
    );

    // With reset inactive, set forces Q high.
    check_set_forces_q_high: assert property (
        @(posedge C) disable iff (!R) S |=> (Q == 1'b1)
    );

    // With reset inactive and set low, D=0 is captured into Q.
    check_capture_d_zero: assert property (
        @(posedge C) disable iff (!R) (!S && !D) |=> (Q == 1'b0)
    );

    // With reset inactive and set low, D=1 is captured into Q.
    check_capture_d_one: assert property (
        @(posedge C) disable iff (!R) (!S && D) |=> (Q == 1'b1)
    );

endmodule