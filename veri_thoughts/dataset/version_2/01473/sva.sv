module mux_2to1_enable_sva (
    input logic CLK,
    input logic A,
    input logic B,
    input logic E,
    input logic Y
);

    // Y implements a 2:1 mux: Y == (E ? A : B).
    check_mux_function: assert property (
        @(posedge CLK) Y == (E ? A : B)
    );

    // When E=1, Y must equal A.
    check_select_a_when_e1: assert property (
        @(posedge CLK) (E == 1'b1) |-> (Y == A)
    );

    // When E=0, Y must equal B.
    check_select_b_when_e0: assert property (
        @(posedge CLK) (E == 1'b0) |-> (Y == B)
    );

    // With E=0 and only A changing, Y must remain stable.
    check_a_ignored_when_e0: assert property (
        @(posedge CLK) (E == 1'b0 && $stable(E) && $stable(B) && $changed(A)) |-> $stable(Y)
    );

    // With E=1 and only B changing, Y must remain stable.
    check_b_ignored_when_e1: assert property (
        @(posedge CLK) (E == 1'b1 && $stable(E) && $stable(A) && $changed(B)) |-> $stable(Y)
    );

    // If A and B are equal, Y must equal that value regardless of E.
    check_equal_inputs_passthrough: assert property (
        @(posedge CLK) (A == B) |-> (Y == A)
    );

    // If A and B are stable and equal while E toggles, Y must remain stable.
    check_e_toggle_no_effect_when_a_eq_b: assert property (
        @(posedge CLK) ($stable(A) && $stable(B) && (A == B) && $changed(E)) |-> $stable(Y)
    );

endmodule