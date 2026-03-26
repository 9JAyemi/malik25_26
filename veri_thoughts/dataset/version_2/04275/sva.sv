module buf2_sva (
    input logic A,
    input logic B,
    input logic CLK,
    input logic EN,
    input logic CLR,
    input logic X,
    input logic Y,
    input logic X_buf,
    input logic Y_buf,
    input logic [1:0] state
);

    // X and Y directly reflect the internal buffer registers.
    check_outputs_match_buffers: assert property (
        @(posedge CLK) disable iff (CLR)
        (X == X_buf) && (Y == Y_buf)
    );

    // On the first cycle after reset, state and outputs remain cleared.
    check_reset_clears_all: assert property (
        @(posedge CLK) disable iff (CLR)
        $past(CLR) |-> (state == 2'd0) && (X_buf == 1'b0) && (Y_buf == 1'b0) && (X == 1'b0) && (Y == 1'b0)
    );

    // In state 0 with EN high, capture A/B and advance to state 1.
    check_state0_captures_inputs: assert property (
        @(posedge CLK) disable iff (CLR)
        (state == 2'd0 && EN) |=> (state == 2'd1) &&
                                 (X_buf == $past(A)) && (Y_buf == $past(B)) &&
                                 (X == $past(A)) && (Y == $past(B))
    );

    // In state 1 with EN high, hold the buffers and advance to state 2.
    check_state1_holds_and_advances: assert property (
        @(posedge CLK) disable iff (CLR)
        (state == 2'd1 && EN) |=> (state == 2'd2) &&
                                 (X_buf == $past(X_buf)) && (Y_buf == $past(Y_buf)) &&
                                 (X == $past(X)) && (Y == $past(Y))
    );

    // In state 2 with EN high, hold the buffers and wrap back to state 0.
    check_state2_holds_and_wraps: assert property (
        @(posedge CLK) disable iff (CLR)
        (state == 2'd2 && EN) |=> (state == 2'd0) &&
                                 (X_buf == $past(X_buf)) && (Y_buf == $past(Y_buf)) &&
                                 (X == $past(X)) && (Y == $past(Y))
    );

    // With EN low, the state and outputs hold their previous values.
    check_en_low_holds_registers: assert property (
        @(posedge CLK) disable iff (CLR)
        (!EN) |=> (state == $past(state)) &&
                  (X_buf == $past(X_buf)) && (Y_buf == $past(Y_buf)) &&
                  (X == $past(X)) && (Y == $past(Y))
    );

    // With EN high in unhandled state 3, no registers are updated.
    check_state3_holds_without_case_match: assert property (
        @(posedge CLK) disable iff (CLR)
        (state == 2'd3 && EN) |=> (state == 2'd3) &&
                                 (X_buf == $past(X_buf)) && (Y_buf == $past(Y_buf)) &&
                                 (X == $past(X)) && (Y == $past(Y))
    );

endmodule