module shift_register_sva (
    input logic clk,
    input logic d,
    input logic [2:0] q
);
    // q[0] captures d=1 on the next rising edge.
    check_q0_captures_d_high: assert property (
        @(posedge clk) (d == 1'b1) |-> ##1 (q[0] == 1'b1)
    );

    // q[0] captures d=0 on the next rising edge.
    check_q0_captures_d_low: assert property (
        @(posedge clk) (d == 1'b0) |-> ##1 (q[0] == 1'b0)
    );

    // q[1] captures q[0]=1 on the next rising edge.
    check_q1_captures_q0_high: assert property (
        @(posedge clk) (q[0] == 1'b1) |-> ##1 (q[1] == 1'b1)
    );

    // q[1] captures q[0]=0 on the next rising edge.
    check_q1_captures_q0_low: assert property (
        @(posedge clk) (q[0] == 1'b0) |-> ##1 (q[1] == 1'b0)
    );

    // q[2] captures q[1]=1 on the next rising edge.
    check_q2_captures_q1_high: assert property (
        @(posedge clk) (q[1] == 1'b1) |-> ##1 (q[2] == 1'b1)
    );

    // q[2] captures q[1]=0 on the next rising edge.
    check_q2_captures_q1_low: assert property (
        @(posedge clk) (q[1] == 1'b0) |-> ##1 (q[2] == 1'b0)
    );

    // q[1] equals d after two rising edges when d=1.
    check_d_to_q1_after_2_high: assert property (
        @(posedge clk) (d == 1'b1) |-> ##2 (q[1] == 1'b1)
    );

    // q[1] equals d after two rising edges when d=0.
    check_d_to_q1_after_2_low: assert property (
        @(posedge clk) (d == 1'b0) |-> ##2 (q[1] == 1'b0)
    );

    // q[2] equals d after three rising edges when d=1.
    check_d_to_q2_after_3_high: assert property (
        @(posedge clk) (d == 1'b1) |-> ##3 (q[2] == 1'b1)
    );

    // q[2] equals d after three rising edges when d=0.
    check_d_to_q2_after_3_low: assert property (
        @(posedge clk) (d == 1'b0) |-> ##3 (q[2] == 1'b0)
    );
endmodule