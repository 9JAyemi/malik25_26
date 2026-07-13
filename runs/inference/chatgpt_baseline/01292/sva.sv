module seq_detector_sva (
    input logic clk,
    input logic in,
    input logic out,
    input logic [1:0] state,
    input logic [1:0] next_state
);

    // Mirror DUT parameters for readability
    localparam logic [1:0] state0 = 2'b00;
    localparam logic [1:0] state1 = 2'b01;
    localparam logic [1:0] state2 = 2'b10;

    ///// Output definition /////
    // out is 1 iff state == state2.
    check_out_definition: assert property (
        @(posedge clk) out == (state == state2)
    );

    ///// Combinational next-state logic (sampled on clk) /////
    // With in==0, next_state is always state0.
    check_next_state_in0: assert property (
        @(posedge clk) (in == 1'b0) |-> (next_state == state0)
    );
    // From state0 with in==1, next_state is state1.
    check_next_state_s0_in1: assert property (
        @(posedge clk) (state == state0 && in == 1'b1) |-> (next_state == state1)
    );
    // From state1 with in==1, next_state is state2.
    check_next_state_s1_in1: assert property (
        @(posedge clk) (state == state1 && in == 1'b1) |-> (next_state == state2)
    );
    // From state2 with in==1, next_state stays state2.
    check_next_state_s2_in1: assert property (
        @(posedge clk) (state == state2 && in == 1'b1) |-> (next_state == state2)
    );
    // next_state is always one of the defined encodings.
    check_next_state_encoding: assert property (
        @(posedge clk) next_state inside {state0, state1, state2}
    );
    // For any invalid state encoding, next_state resolves to state0 via default.
    check_default_invalid_to_s0: assert property (
        @(posedge clk) !(state inside {state0, state1, state2}) |-> (next_state == state0)
    );

    ///// Sequential state update /////
    // On each clock (after the first), state updates to previous next_state.
    check_state_follows_next: assert property (
        @(posedge clk) $past(1'b1) |-> (state == $past(next_state))
    );

    ///// End-to-end transition effects (prev inputs/states to current state/out) /////
    // If previous in==0, state becomes state0 and out is 0.
    check_prev_in0_state0_out0: assert property (
        @(posedge clk) $past(in == 1'b0) |-> (state == state0 && out == 1'b0)
    );
    // From state0 with previous in==1, move to state1 and out is 0.
    check_prev_s0_in1_to_s1_out0: assert property (
        @(posedge clk) $past(state == state0 && in == 1'b1) |-> (state == state1 && out == 1'b0)
    );
    // From state1 with previous in==1, move to state2 and out is 1.
    check_prev_s1_in1_to_s2_out1: assert property (
        @(posedge clk) $past(state == state1 && in == 1'b1) |-> (state == state2 && out == 1'b1)
    );
    // From state2 with previous in==1, stay in state2 and out is 1.
    check_prev_s2_in1_stay_s2_out1: assert property (
        @(posedge clk) $past(state == state2 && in == 1'b1) |-> (state == state2 && out == 1'b1)
    );

endmodule