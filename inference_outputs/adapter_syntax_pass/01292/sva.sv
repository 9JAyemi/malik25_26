module seq_detector_sva (
    input logic in,
    input logic out,
    input logic clk,
    input logic [1:0] state,
    input logic [1:0] next_state
);

    localparam logic [1:0] state0 = 2'b00;
    localparam logic [1:0] state1 = 2'b01;
    localparam logic [1:0] state2 = 2'b10;

    // next_state matches the RTL case statement for state0.
    check_next_state_state0: assert property (
        @(posedge clk) (state == state0) |-> (next_state == ((in == 1'b0) ? state0 : state1))
    );

    // next_state matches the RTL case statement for state1.
    check_next_state_state1: assert property (
        @(posedge clk) (state == state1) |-> (next_state == ((in == 1'b0) ? state0 : state2))
    );

    // next_state matches the RTL case statement for state2.
    check_next_state_state2: assert property (
        @(posedge clk) (state == state2) |-> (next_state == ((in == 1'b0) ? state0 : state2))
    );

    // next_state matches the RTL default case for all other states.
    check_next_state_default: assert property (
        @(posedge clk) (state != state0 && state != state1 && state != state2) |-> (next_state == state0)
    );

    // state updates to next_state on each clock.
    check_state_updates_from_next_state: assert property (
        @(posedge clk) 1'b1 |=> (state == $past(next_state))
    );

    // out is high exactly when state is state2.
    check_out_matches_state: assert property (
        @(posedge clk) (out == (state == state2))
    );

    // out is low on the first clock after reset.
    check_out_low_after_reset: assert property (
        @(posedge clk) 1'b1 |=> (out == 1'b0)
    );

    // state0 holds when in is low.
    check_state0_holds_on_low_input: assert property (
        @(posedge clk) (state == state0 && in == 1'b0) |=> (state == state0)
    );

    // state0 advances to state1 when in is high.
    check_state0_advances_on_high_input: assert property (
        @(posedge clk) (state == state0 && in == 1'b1) |=> (state == state1)
    );

    // state1 holds when in is low.
    check_state1_holds_on_low_input: assert property (
        @(posedge clk) (state == state1 && in == 1'b0) |=> (state == state1)
    );

    // state1 advances to state2 when in is high.
    check_state1_advances_on_high_input: assert property (
        @(posedge clk) (state == state1 && in == 1'b1) |=> (state == state2)
    );

    // state2 holds when in is low.
    check_state2_holds_on_low_input: assert property (
        @(posedge clk) (state == state2 && in == 1'b0) |=> (state == state2)
    );

    // state2 repeats when in is high.
    check_state2_repeats_on_high_input: assert property (
        @(posedge clk) (state == state2 && in == 1'b1) |=> (state == state2)
    );

endmodule