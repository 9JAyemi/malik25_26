module mux_2_to_1_sva (
    input logic clk,
    input logic Y,
    input logic A,
    input logic B,
    input logic S
);

    // When S is low, Y selects A.
    check_select_a: assert property (
        @(posedge clk) (S === 1'b0) |-> (Y === A)
    );

    // When S is high, Y selects B.
    check_select_b: assert property (
        @(posedge clk) (S === 1'b1) |-> (Y === B)
    );

    // With S held low, a sampled change on A changes Y.
    check_a_change_propagates_when_selected: assert property (
        @(posedge clk) ($past(S) === 1'b0 && S === 1'b0 && $past(A) !== A) |-> ($past(Y) !== Y && Y === A)
    );

    // With S held high, a sampled change on B changes Y.
    check_b_change_propagates_when_selected: assert property (
        @(posedge clk) ($past(S) === 1'b1 && S === 1'b1 && $past(B) !== B) |-> ($past(Y) !== Y && Y === B)
    );

    // With S low and A stable, B does not affect Y.
    check_b_ignored_when_s_low: assert property (
        @(posedge clk) ($past(S) === 1'b0 && S === 1'b0 && $past(A) === A && $past(B) !== B) |-> ($past(Y) === Y)
    );

    // With S high and B stable, A does not affect Y.
    check_a_ignored_when_s_high: assert property (
        @(posedge clk) ($past(S) === 1'b1 && S === 1'b1 && $past(B) === B && $past(A) !== A) |-> ($past(Y) === Y)
    );

    // A low-to-high selector change makes Y select B.
    check_switch_to_b: assert property (
        @(posedge clk) ($past(S) === 1'b0 && S === 1'b1) |-> (Y === B)
    );

    // A high-to-low selector change makes Y select A.
    check_switch_to_a: assert property (
        @(posedge clk) ($past(S) === 1'b1 && S === 1'b0) |-> (Y === A)
    );

endmodule