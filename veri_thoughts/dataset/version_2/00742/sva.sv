module jfsmMealyWithOverlap_sva (
    input logic clock,
    input logic reset,
    input logic datain,
    input logic dataout,
    input logic [1:0] state
);
    // Local copies of state encodings for readability
    localparam logic [1:0] S0 = 2'b00;
    localparam logic [1:0] S1 = 2'b01;
    localparam logic [1:0] S2 = 2'b10;
    localparam logic [1:0] S3 = 2'b11;

    ///// Reset behavior /////
    // After a cycle with reset asserted, state must be S0.
    after_reset_state_is_S0: assert property (
        @(posedge clock) disable iff (reset) $past(reset) |-> (state == S0)
    );
    // After a cycle with reset asserted, dataout must be 0.
    after_reset_dataout_low: assert property (
        @(posedge clock) disable iff (reset) $past(reset) |-> (dataout == 1'b0)
    );

    ///// State transition rules /////
    // From any state, a 0 input forces next state to S0.
    zero_input_forces_S0_next: assert property (
        @(posedge clock) disable iff (reset) (datain == 1'b0) |=> (state == S0)
    );
    // From S0 with input 1, next state is S1.
    trans_S0_to_S1_on_one: assert property (
        @(posedge clock) disable iff (reset) (state == S0 && datain == 1'b1) |=> (state == S1)
    );
    // From S1 with input 1, next state is S2.
    trans_S1_to_S2_on_one: assert property (
        @(posedge clock) disable iff (reset) (state == S1 && datain == 1'b1) |=> (state == S2)
    );
    // From S2 with input 1, next state is S3.
    trans_S2_to_S3_on_one: assert property (
        @(posedge clock) disable iff (reset) (state == S2 && datain == 1'b1) |=> (state == S3)
    );
    // In S3 with input 1, remain in S3.
    trans_S3_stays_on_one: assert property (
        @(posedge clock) disable iff (reset) (state == S3 && datain == 1'b1) |=> (state == S3)
    );

    ///// Output mapping /////
    // In S3, dataout must be 1 in the same cycle.
    out_high_in_S3: assert property (
        @(posedge clock) disable iff (reset) (state == S3) |-> (dataout == 1'b1)
    );
    // Outside S3, dataout must be 0 in the same cycle.
    out_low_outside_S3: assert property (
        @(posedge clock) disable iff (reset) (state != S3) |-> (dataout == 1'b0)
    );

    ///// Sequence-level behavior /////
    // Three consecutive 1s on datain lead to S3 after the third cycle (overlapped allowed).
    three_ones_lead_to_S3: assert property (
        @(posedge clock) disable iff (reset) (datain == 1'b1)[*3] |=> (state == S3)
    );

endmodule