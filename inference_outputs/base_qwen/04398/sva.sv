module Sec6_SM_assertions (
    input logic clk_i,
    input logic reset_n,
    output logic [2:0] sel
);
    // Sequential logic: state machine with reset
    // State transitions are controlled by the state_next register
    // State_next is updated on the rising edge of clk_i
    state_transition: assert property (
        @(posedge clk_i) disable iff (!reset_n) (state != state_next)
    );

    // State machine should cycle through states S0, S1, S2, S3
    // State S0 should map to sel = 3'b000
    state_S0: assert property (
        @(posedge clk_i) disable iff (!reset_n) (state == 2'b00) |-> (sel == 3'b000)
    );

    // State S1 should map to sel = 3'b001
    state_S1: assert property (
        @(posedge clk_i) disable iff (!reset_n) (state == 2'b01) |-> (sel == 3'b001)
    );

    // State S2 should map to sel = 3'b011
    state_S2: assert property (
        @(posedge clk_i) disable iff (!reset_n) (state == 2'b10) |-> (sel == 3'b011)
    );

    // State S3 should map to sel = 3'b100
    state_S3: assert property (
        @(posedge clk_i) disable iff (!reset_n) (state == 2'b11) |-> (sel == 3'b100)
    );

    // At reset, state should be S0 and sel should be 3'b000
    reset_state: assert property (
        @(posedge clk_i) !reset_n |-> (state == 2'b00) && (sel == 3'b000)
    );

    // State_next should always be one of the valid states S0, S1, S2, S3
    state_next_valid: assert property (
        @(posedge clk_i) disable iff (!reset_n) (state_next == 2'b00 || state_next == 2'b01 || state_next == 2'b10 || state_next == 2'b11)
    );

    // State should not be in an invalid state
    state_valid: assert property (
        @(posedge clk_i) disable iff (!reset_n) (state == 2'b00 || state == 2'b01 || state == 2'b10 || state == 2'b11)
    );

    // sel should always be one of the valid values 3'b000, 3'b001, 3'b011, 3'b100
    sel_valid: assert property (
        @(posedge clk_i) disable iff (!reset_n) (sel == 3'b000 || sel == 3'b001 || sel == 3'b011 || sel == 3'b100)
    );

    // State transition should not be to the same state
    no_self_transition: assert property (
        @(posedge clk_i) disable iff (!reset_n) (state != state_next)
    );

    // State should not be in an invalid state
    state_not_invalid: assert property (
        @(posedge clk_i) disable iff (!reset_n) (state == 2'b00 || state == 2'b01 || state == 2'b10 || state == 2'b11)
    );
endmodule