module seq_detector_sva (
    input logic in,
    input logic out,
    input logic clk,
    input logic [1:0] state,
    input logic [1:0] next_state
);

// Next-state function matches RTL for state0.
    check_next_state_state0: assert property (
        @(posedge clk) disable iff (1'b0)
        (state == state0) |-> (next_state == ((in == 1'b0) ? state0 : state1))
    );

// Next-state function matches RTL for state1.
    check_next_state_state1: assert property (
        @(posedge clk) disable iff (1'b0)
        (state == state1) |-> (next_state == ((in == 1'b0) ? state0 : state2))
    );

// Next-state function matches RTL for state2.
    check_next_state_state2: assert property (
        @(posedge clk) disable iff (1'b0)
        (state == state2) |-> (next_state == ((in == 1'b0) ? state0 : state2))
    );

// Output is high only when in is high and previous input was high.
    check_out_high_condition: assert property (
        @(posedge clk) disable iff (1'b0)
        (out == 1'b1) |-> ((in == 1'b1) && ($past(in) == 1'b1))
    );

// Output is low when in is low or previous input was low.
    check_out_low_condition: assert property (
        @(posedge clk) disable iff (1'b0)
        (out == 1'b0) |-> ((in == 1'b0) || ($past(in) == 1'b0))
    );

// If in is low, next_state must be state0 on the next cycle.
    check_next_state_low_input: assert property (
        @(posedge clk) disable iff (1'b0)
        (in == 1'b0) |-> ##1 (next_state == state0)
    );

// If in is high and previous input was high, next_state must be state2.
    check_next_state_high_high_prev: assert property (
        @(posedge clk) disable iff (1'b0)
        (in == 1'b1) && ($past(in) == 1'b1) |-> ##1 (next_state == state2)
    );

// If in is high and previous input was low, next_state must be state1.
    check_next_state_high_low_prev: assert property (
        @(posedge clk) disable iff (1'b0)
        (in == 1'b1) && ($past(in) == 1'b0) |-> ##1 (next_state == state1)
    );

endmodule
