module mux_2to1_sva (
    input logic D0,
    input logic D1,
    input logic S,
    input logic RST,
    input logic CLK,
    input logic Y
);

    // Reset drives Y to 0 on the cycle after any reset-high clock.
    check_reset_clears_y_next: assert property (
        @(posedge CLK) RST |=> (Y == 1'b0)
    );

    // With S=1 and no reset, Y updates next cycle with prior D1.
    check_select_d1_path: assert property (
        @(posedge CLK) disable iff (RST) (S == 1'b1) |=> (Y == $past(D1))
    );

    // With S=0 and no reset, Y updates next cycle with prior D0.
    check_select_d0_path: assert property (
        @(posedge CLK) disable iff (RST) (S == 1'b0) |=> (Y == $past(D0))
    );

    // If previous cycle was not in reset, Y equals the previously selected input.
    check_y_matches_prev_selection: assert property (
        @(posedge CLK) disable iff (RST) !$past(RST) |-> (Y == ($past(S) ? $past(D1) : $past(D0)))
    );

    // When inputs are equal and not in reset, Y equals that common value next cycle.
    check_equal_inputs_case: assert property (
        @(posedge CLK) disable iff (RST) (!RST && (D0 == D1)) |=> (Y == $past(D0))
    );

endmodule