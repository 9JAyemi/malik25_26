module Sec6_SM_sva (
    input logic       clk_i,
    input logic       reset_n,
    input logic [2:0] sel,
    input logic [1:0] state,
    input logic [1:0] state_next
);

    localparam logic [1:0] S0 = 2'b00;
    localparam logic [1:0] S1 = 2'b01;
    localparam logic [1:0] S2 = 2'b10;
    localparam logic [1:0] S3 = 2'b11;

    // Reset forces the state register to S0.
    check_reset_forces_state_s0: assert property (
        @(posedge clk_i) !reset_n |-> (state == S0)
    );

    // Reset drives sel to the S0 decode value.
    check_reset_drives_sel_s0: assert property (
        @(posedge clk_i) !reset_n |-> (sel == 3'b000)
    );

    // S0 computes S1 as the next state.
    check_state_next_from_s0: assert property (
        @(posedge clk_i) disable iff (!reset_n)
        (state == S0) |-> (state_next == S1)
    );

    // S1 computes S2 as the next state.
    check_state_next_from_s1: assert property (
        @(posedge clk_i) disable iff (!reset_n)
        (state == S1) |-> (state_next == S2)
    );

    // S2 computes S3 as the next state.
    check_state_next_from_s2: assert property (
        @(posedge clk_i) disable iff (!reset_n)
        (state == S2) |-> (state_next == S3)
    );

    // S3 computes S0 as the next state.
    check_state_next_from_s3: assert property (
        @(posedge clk_i) disable iff (!reset_n)
        (state == S3) |-> (state_next == S0)
    );

    // The FSM advances from S0 to S1 on the next clock.
    check_state_advances_s0_to_s1: assert property (
        @(posedge clk_i) disable iff (!reset_n)
        (state == S0) |=> (state == S1)
    );

    // The FSM advances from S1 to S2 on the next clock.
    check_state_advances_s1_to_s2: assert property (
        @(posedge clk_i) disable iff (!reset_n)
        (state == S1) |=> (state == S2)
    );

    // The FSM advances from S2 to S3 on the next clock.
    check_state_advances_s2_to_s3: assert property (
        @(posedge clk_i) disable iff (!reset_n)
        (state == S2) |=> (state == S3)
    );

    // The FSM advances from S3 to S0 on the next clock.
    check_state_advances_s3_to_s0: assert property (
        @(posedge clk_i) disable iff (!reset_n)
        (state == S3) |=> (state == S0)
    );

    // S0 decodes to sel = 000.
    check_sel_decode_s0: assert property (
        @(posedge clk_i) disable iff (!reset_n)
        (state == S0) |-> (sel == 3'b000)
    );

    // S1 decodes to sel = 001.
    check_sel_decode_s1: assert property (
        @(posedge clk_i) disable iff (!reset_n)
        (state == S1) |-> (sel == 3'b001)
    );

    // S2 decodes to sel = 011.
    check_sel_decode_s2: assert property (
        @(posedge clk_i) disable iff (!reset_n)
        (state == S2) |-> (sel == 3'b011)
    );

    // S3 decodes to sel = 100.
    check_sel_decode_s3: assert property (
        @(posedge clk_i) disable iff (!reset_n)
        (state == S3) |-> (sel == 3'b100)
    );

    // sel only takes one of the implemented decode values.
    check_sel_legal_values: assert property (
        @(posedge clk_i) disable iff (!reset_n)
        (sel == 3'b000) || (sel == 3'b001) || (sel == 3'b011) || (sel == 3'b100)
    );

endmodule