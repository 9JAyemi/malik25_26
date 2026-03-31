module Sec6_SM_sva (
    input logic clk_i,
    input logic reset_n,
    input logic [2:0] sel,
    input logic [1:0] state,
    input logic [1:0] state_next
);

    // Reset forces the state machine into S0.
    check_reset_state: assert property (
        @(posedge clk_i) !reset_n |-> (state == 2'b00)
    );

    // Reset forces the selected output to 000.
    check_reset_sel: assert property (
        @(posedge clk_i) !reset_n |-> (sel == 3'b000)
    );

    // State S0 maps to sel 000.
    check_s0_sel_mapping: assert property (
        @(posedge clk_i) disable iff (!reset_n) (state == 2'b00) |-> (sel == 3'b000)
    );

    // State S1 maps to sel 001.
    check_s1_sel_mapping: assert property (
        @(posedge clk_i) disable iff (!reset_n) (state == 2'b01) |-> (sel == 3'b001)
    );

    // State S2 maps to sel 011.
    check_s2_sel_mapping: assert property (
        @(posedge clk_i) disable iff (!reset_n) (state == 2'b10) |-> (sel == 3'b011)
    );

    // State S3 maps to sel 100.
    check_s3_sel_mapping: assert property (
        @(posedge clk_i) disable iff (!reset_n) (state == 2'b11) |-> (sel == 3'b100)
    );

    // State S0 drives the next state to S1.
    check_s0_next_state: assert property (
        @(posedge clk_i) disable iff (!reset_n) (state == 2'b00) |-> (state_next == 2'b01)
    );

    // State S1 drives the next state to S2.
    check_s1_next_state: assert property (
        @(posedge clk_i) disable iff (!reset_n) (state == 2'b01) |-> (state_next == 2'b10)
    );

    // State S2 drives the next state to S3.
    check_s2_next_state: assert property (
        @(posedge clk_i) disable iff (!reset_n) (state == 2'b10) |-> (state_next == 2'b11)
    );

    // State S3 drives the next state to S0.
    check_s3_next_state: assert property (
        @(posedge clk_i) disable iff (!reset_n) (state == 2'b11) |-> (state_next == 2'b00)
    );

    // Invalid states drive the next state to S0.
    check_invalid_next_state: assert property (
        @(posedge clk_i) disable iff (!reset_n) (state != 2'b00 && state != 2'b01 && state != 2'b10 && state != 2'b11) |-> (state_next == 2'b00)
    );

endmodule