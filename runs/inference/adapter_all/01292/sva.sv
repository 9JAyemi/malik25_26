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

    // next_state follows the RTL case table from state.
    check_next_state_decode: assert property (
        @(posedge clk)
        1'b1 |=> (next_state == ($past(state) == state0 ? ($past(in) ? state1 : state0) :
                                 ($past(state) == state1 ? ($past(in) ? state2 : state0) :
                                 ($past(state) == state2 ? ($past(in) ? state2 : state0) : state0))))
    );

    // state updates from the previous next_state value.
    check_state_updates_from_next_state: assert property (
        @(posedge clk)
        1'b1 |=> (state == $past(next_state))
    );

    // out reflects whether the current state is state2.
    check_out_matches_state: assert property (
        @(posedge clk)
        (out == (state == state2))
    );

    // state0 with in low stays in state0.
    check_state0_low_stays: assert property (
        @(posedge clk)
        (state == state0 && in == 1'b0) |=> (state == state0)
    );

    // state0 with in high goes to state1.
    check_state0_high_to_state1: assert property (
        @(posedge clk)
        (state == state0 && in == 1'b1) |=> (state == state1)
    );

    // state1 with in low goes to state0.
    check_state1_low_to_state0: assert property (
        @(posedge clk)
        (state == state1 && in == 1'b0) |=> (state == state0)
    );

    // state1 with in high goes to state2.
    check_state1_high_to_state2: assert property (
        @(posedge clk)
        (state == state1 && in == 1'b1) |=> (state == state2)
    );

    // state2 with in low goes to state0.
    check_state2_low_to_state0: assert property (
        @(posedge clk)
        (state == state2 && in == 1'b0) |=> (state == state0)
    );

    // state2 with in high stays in state2.
    check_state2_high_stays: assert property (
        @(posedge clk)
        (state == state2 && in == 1'b1) |=> (state == state2)
    );

    // out can only change when the current state is state2.
    check_out_changes_only_from_state2: assert property (
        @(posedge clk)
        $changed(out) |-> (state == state2)
    );

endmodule