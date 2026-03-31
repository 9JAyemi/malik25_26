module Sec6_SM_sva (
    input logic clk_i,
    input logic reset_n,
    input logic [2:0] sel,
    input logic [1:0] state
);

// Reset forces state to S0 on the next cycle.
    check_reset_forces_state_s0: assert property (
        @(posedge clk_i) !reset_n |=> (state == S0)
    );

// Reset forces sel to 000 on the next cycle.
    check_reset_forces_sel_000: assert property (
        @(posedge clk_i) !reset_n |=> (sel == 3'b000)
    );

// State transitions from S0 to S1 on the next cycle.
    check_state_s0_to_s1: assert property (
        @(posedge clk_i) disable iff (!reset_n) (state == S0) |=> (state == S1)
    );

// State transitions from S1 to S2 on the next cycle.
    check_state_s1_to_s2: assert property (
        @(posedge clk_i) disable iff (!reset_n) (state == S1) |=> (state == S2)
    );

// State transitions from S2 to S3 on the next cycle.
    check_state_s2_to_s3: assert property (
        @(posedge clk_i) disable iff (!reset_n) (state == S2) |=> (state == S3)
    );

// State transitions from S3 back to S0 on the next cycle.
    check_state_s3_to_s0: assert property (
        @(posedge clk_i) disable iff (!reset_n) (state == S3) |=> (state == S0)
    );

// sel is 000 when state is S0.
    check_sel_000_when_state_s0: assert property (
        @(posedge clk_i) disable iff (!reset_n) (state == S0) |-> (sel == 3'b000)
    );

// sel is 001 when state is S1.
    check_sel_001_when_state_s1: assert property (
        @(posedge clk_i) disable iff (!reset_n) (state == S1) |-> (sel == 3'b001)
    );

// sel is 011 when state is S2.
    check_sel_011_when_state_s2: assert property (
        @(posedge clk_i) disable iff (!reset_n) (state == S2) |-> (sel == 3'b011)
    );

// sel is 100 when state is S3.
    check_sel_100_when_state_s3: assert property (
        @(posedge clk_i) disable iff (!reset_n) (state == S3) |-> (sel == 3'b100)
    );

endmodule
