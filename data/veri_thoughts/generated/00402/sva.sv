module arithmetic_circuit_sva (
    input logic clock,
    input logic c_in,
    input logic d_in,
    input logic out1,
    input logic temp
);

    // temp captures the prior cycle c_in - d_in value.
    check_temp_tracks_input_difference: assert property (
        @(posedge clock) disable iff ($initstate)
        temp == $past(c_in - d_in)
    );

    // out1 captures the prior cycle temp - d_in value.
    check_out1_tracks_temp_difference: assert property (
        @(posedge clock) disable iff ($initstate)
        out1 == $past(temp - d_in)
    );

    // Equal c_in and d_in produce a zero temp on the next cycle.
    check_temp_zero_when_inputs_equal: assert property (
        @(posedge clock) disable iff ($initstate)
        $past(c_in == d_in) |-> (temp == 1'b0)
    );

    // Different c_in and d_in produce a one temp on the next cycle.
    check_temp_one_when_inputs_differ: assert property (
        @(posedge clock) disable iff ($initstate)
        $past(c_in != d_in) |-> (temp == 1'b1)
    );

    // Equal temp and d_in produce a zero out1 on the next cycle.
    check_out1_zero_when_temp_matches_d: assert property (
        @(posedge clock) disable iff ($initstate)
        $past(temp == d_in) |-> (out1 == 1'b0)
    );

    // Different temp and d_in produce a one out1 on the next cycle.
    check_out1_one_when_temp_differs_from_d: assert property (
        @(posedge clock) disable iff ($initstate)
        $past(temp != d_in) |-> (out1 == 1'b1)
    );

endmodule