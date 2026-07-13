module mux_2to1_assertions (
    input logic A,
    input logic B,
    input logic S,
    input logic CLK,
    input logic Y
);

    // When select is exactly 0, Y captures A on the following clock.
    check_capture_a_when_s_low: assert property (
        @(posedge CLK) (S === 1'b0) |=> (Y == $past(A))
    );

    // When select is not exactly 0, Y captures B on the following clock.
    check_capture_b_when_s_not_low: assert property (
        @(posedge CLK) (S !== 1'b0) |=> (Y == $past(B))
    );

    // Y always reflects the input selected on the previous clock edge.
    check_output_matches_previous_selection: assert property (
        @(posedge CLK) 1'b1 |=> (Y == (($past(S) === 1'b0) ? $past(A) : $past(B)))
    );

endmodule