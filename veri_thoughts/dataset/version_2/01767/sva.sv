module p_aoi22_sva (
    input logic clk,
    input logic q,
    input logic qbar,
    input logic i0,
    input logic i1,
    input logic i2,
    input logic i3
);
    // q equals (i0|i1|~i2|~i3).
    check_q_functional: assert property (
        @(posedge clk) q == ((i0 | i1) | ((~i2) | (~i3)))
    );

    // qbar equals (i0|i1) & ~q.
    check_qbar_functional: assert property (
        @(posedge clk) qbar == ((i0 | i1) & (~q))
    );

    // qbar is always 0 due to logic structure.
    check_qbar_always_zero: assert property (
        @(posedge clk) qbar == 1'b0
    );

    // If i0 is 1 then q must be 1.
    check_q_high_when_i0_high: assert property (
        @(posedge clk) i0 |-> (q == 1'b1)
    );

    // If i1 is 1 then q must be 1.
    check_q_high_when_i1_high: assert property (
        @(posedge clk) i1 |-> (q == 1'b1)
    );

    // If i2 is 0 then q must be 1.
    check_q_high_when_i2_low: assert property (
        @(posedge clk) (~i2) |-> (q == 1'b1)
    );

    // If i3 is 0 then q must be 1.
    check_q_high_when_i3_low: assert property (
        @(posedge clk) (~i3) |-> (q == 1'b1)
    );

    // If i0=0,i1=0,i2=1,i3=1 then q must be 0.
    check_q_low_under_specific_inputs: assert property (
        @(posedge clk) ((~i0) && (~i1) && i2 && i3) |-> (q == 1'b0)
    );

    // q is 0 only when i0=0,i1=0,i2=1,i3=1.
    check_q_low_only_if_specific_inputs: assert property (
        @(posedge clk) (q == 1'b0) |-> ((~i0) && (~i1) && i2 && i3)
    );

    // When i0=0 and i1=0, qbar must be 0.
    check_qbar_zero_when_no_i0_i1: assert property (
        @(posedge clk) ((~i0) && (~i1)) |-> (qbar == 1'b0)
    );

    // If q is 1 then qbar must be 0.
    check_qbar_zero_when_q_one: assert property (
        @(posedge clk) (q == 1'b1) |-> (qbar == 1'b0)
    );

    // q and qbar are never both 1.
    check_q_qbar_never_both_one: assert property (
        @(posedge clk) !(q && qbar)
    );
endmodule