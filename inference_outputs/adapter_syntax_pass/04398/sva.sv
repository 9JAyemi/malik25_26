module Sec6_SM_sva (
    input logic clk_i,
    input logic reset_n,
    input logic [2:0] sel,
    input logic [1:0] state
);

    localparam logic [1:0] S0 = 2'b00;
    localparam logic [1:0] S1 = 2'b01;
    localparam logic [1:0] S2 = 2'b10;
    localparam logic [1:0] S3 = 2'b11;

    // Reset forces the state machine into S0.
    check_reset_state: assert property (
        @(posedge clk_i) !reset_n |-> (state == S0)
    );

    // Reset forces the selected output to 000.
    check_reset_sel: assert property (
        @(posedge clk_i) !reset_n |-> (sel == 3'b000)
    );

    // S0 drives sel to 000.
    check_s0_sel: assert property (
        @(posedge clk_i) disable iff (!reset_n) (state == S0) |-> (sel == 3'b000)
    );

    // S1 drives sel to 001.
    check_s1_sel: assert property (
        @(posedge clk_i) disable iff (!reset_n) (state == S1) |-> (sel == 3'b001)
    );

    // S2 drives sel to 011.
    check_s2_sel: assert property (
        @(posedge clk_i) disable iff (!reset_n) (state == S2) |-> (sel == 3'b011)
    );

    // S3 drives sel to 100.
    check_s3_sel: assert property (
        @(posedge clk_i) disable iff (!reset_n) (state == S3) |-> (sel == 3'b100)
    );

    // S0 advances to S1 on the next clock.
    check_s0_to_s1: assert property (
        @(posedge clk_i) disable iff (!reset_n) (state == S0) |=> (state == S1)
    );

    // S1 advances to S2 on the next clock.
    check_s1_to_s2: assert property (
        @(posedge clk_i) disable iff (!reset_n) (state == S1) |=> (state == S2)
    );

    // S2 advances to S3 on the next clock.
    check_s2_to_s3: assert property (
        @(posedge clk_i) disable iff (!reset_n) (state == S2) |=> (state == S3)
    );

    // S3 returns to S0 on the next clock.
    check_s3_to_s0: assert property (
        @(posedge clk_i) disable iff (!reset_n) (state == S3) |=> (state == S0)
    );

endmodule