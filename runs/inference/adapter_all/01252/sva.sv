module inverter_sva (
    input logic clk,
    input logic I,
    input logic O
);
    // Output equals bitwise NOT of input.
    check_inverter_function: assert property (
        @(posedge clk) O == ~I
    );

    // If input is 0, output is 1.
    check_inverter_zero_input: assert property (
        @(posedge clk) (I == 1'b0) |-> (O == 1'b1)
    );

    // If input is 1, output is 0.
    check_inverter_one_input: assert property (
        @(posedge clk) (I == 1'b1) |-> (O == 1'b0)
    );

    // If input is X/Z, output is X/Z.
    check_inverter_unknown_input: assert property (
        @(posedge clk) $isunknown(I) |-> $isunknown(O)
    );

    // If input is stable, output is stable.
    check_inverter_stable_when_input_stable: assert property (
        @(posedge clk) $stable(I) |-> $stable(O)
    );

    // If input changes, output changes.
    check_inverter_output_changes_with_input: assert property (
        @(posedge clk) $changed(I) |-> $changed(O)
    );
endmodule

module and_gate_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic Y
);
    // Output equals bitwise AND of inputs.
    check_and_function: assert property (
        @(posedge clk) Y == (A & B)
    );

    // If both inputs are 1, output is 1.
    check_and_both_one: assert property (
        @(posedge clk) (A == 1'b1 && B == 1'b1) |-> (Y == 1'b1)
    );

    // If A is 0, output is 0.
    check_and_a_zero: assert property (
        @(posedge clk) (A == 1'b0) |-> (Y == 1'b0)
    );

    // If B is 0, output is 0.
    check_and_b_zero: assert property (
        @(posedge clk) (B == 1'b0) |-> (Y == 1'b0)
    );

    // If either input is X/Z, output is X/Z.
    check_and_unknown_input: assert property (
        @(posedge clk) ($isunknown(A) || $isunknown(B)) |-> $isunknown(Y)
    );

    // If both inputs are stable, output is stable.
    check_and_stable_when_inputs_stable: assert property (
        @(posedge clk) ($stable(A) && $stable(B)) |-> $stable(Y)
    );

    // If either input changes, output changes.
    check_and_output_changes_with_input: assert property (
        @(posedge clk) ($changed(A) || $changed(B)) |-> $changed(Y)
    );
endmodule

module mux_2to1_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic S,
    input logic Y
);
    // Output equals selected input.
    check_mux_function: assert property (
        @(posedge clk) Y == (S ? B : A)
    );

    // When select is 0, output equals A.
    check_mux_select_zero: assert property (
        @(posedge clk) (S == 1'b0) |-> (Y == A)
    );

    // When select is 1, output equals B.
    check_mux_select_one: assert property (
        @(posedge clk) (S == 1'b1) |-> (Y == B)
    );

    // If select is X/Z, output is X/Z.
    check_mux_unknown_select: assert property (
        @(posedge clk) $isunknown(S) |-> $isunknown(Y)
    );

    // If both inputs are stable, output is stable.
    check_mux_stable_when_inputs_stable: assert property (
        @(posedge clk) ($stable(A) && $stable(B)) |-> $stable(Y)
    );

    // If select and both inputs are stable, output is stable.
    check_mux_stable_when_select_and_inputs_stable: assert property (
        @(posedge clk) ($stable(S) && $stable(A) && $stable(B)) |-> $stable(Y)
    );

    // If select changes and both inputs are stable, output changes.
    check_mux_output_changes_with_select: assert property (
        @(posedge clk) ($changed(S) && $stable(A) && $stable(B)) |-> $changed(Y)
    );

    // If select is 0 and A changes, output changes.
    check_mux_output_changes_with_a_when_select_zero: assert property (
        @(posedge clk) (S == 1'b0 && $changed(A)) |-> $changed(Y)
    );

    // If select is 1 and B changes, output changes.
    check_mux_output_changes_with_b_when_select_one: assert property (
        @(posedge clk) (S == 1'b1 && $changed(B)) |-> $changed(Y)
    );
endmodule