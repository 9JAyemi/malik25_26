module xnor3_2_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic X
);

    // X must equal the 3-input XNOR of A, B, and C.
    check_x_matches_three_input_xnor: assert property (
        @(posedge clk) X == ~(A ^ B ^ C)
    );

    // Even input parity drives X high.
    check_x_high_on_even_parity: assert property (
        @(posedge clk) ((A ^ B ^ C) == 1'b0) |-> (X == 1'b1)
    );

    // Odd input parity drives X low.
    check_x_low_on_odd_parity: assert property (
        @(posedge clk) ((A ^ B ^ C) == 1'b1) |-> (X == 1'b0)
    );

    // X stays stable when all inputs stay stable.
    check_x_stable_when_inputs_stable: assert property (
        @(posedge clk) (!$initstate && $stable({A, B, C})) |-> $stable(X)
    );

    // Changing only A toggles X.
    check_x_toggles_when_a_changes_alone: assert property (
        @(posedge clk) (!$initstate && $changed(A) && $stable(B) && $stable(C)) |-> $changed(X)
    );

    // Changing only B toggles X.
    check_x_toggles_when_b_changes_alone: assert property (
        @(posedge clk) (!$initstate && $stable(A) && $changed(B) && $stable(C)) |-> $changed(X)
    );

    // Changing only C toggles X.
    check_x_toggles_when_c_changes_alone: assert property (
        @(posedge clk) (!$initstate && $stable(A) && $stable(B) && $changed(C)) |-> $changed(X)
    );

    // Changing any two inputs together keeps X stable.
    check_x_stable_when_two_inputs_change: assert property (
        @(posedge clk)
        (!$initstate &&
         (($changed(A) && $changed(B) && $stable(C)) ||
          ($changed(A) && $stable(B) && $changed(C)) ||
          ($stable(A) && $changed(B) && $changed(C))))
        |-> $stable(X)
    );

    // Changing all three inputs together toggles X.
    check_x_toggles_when_all_inputs_change: assert property (
        @(posedge clk) (!$initstate && $changed(A) && $changed(B) && $changed(C)) |-> $changed(X)
    );

endmodule