module my_module_sva (
    input logic X,
    input logic A1,
    input logic A2
);
    // X equals logical AND of A1 and A2.
    check_and_function: assert property (
        @(posedge $global_clock) X == (A1 & A2)
    );

    // X can be 1 only when both A1 and A2 are 1.
    check_X_high_only_when_both_high: assert property (
        @(posedge $global_clock) X |-> (A1 && A2)
    );

    // If A1 is 0 then X must be 0.
    check_A1_zero_forces_X_zero: assert property (
        @(posedge $global_clock) (A1 == 1'b0) |-> (X == 1'b0)
    );

    // If A2 is 0 then X must be 0.
    check_A2_zero_forces_X_zero: assert property (
        @(posedge $global_clock) (A2 == 1'b0) |-> (X == 1'b0)
    );

    // If both inputs are 1 then X must be 1.
    check_both_ones_implies_X_one: assert property (
        @(posedge $global_clock) (A1 && A2) |-> (X == 1'b1)
    );

    // Output changes only when at least one input changes.
    check_output_change_implies_input_change: assert property (
        @(posedge $global_clock) $changed(X) |-> ($changed(A1) || $changed(A2))
    );

    // If inputs are stable then output is stable.
    check_stability_with_stable_inputs: assert property (
        @(posedge $global_clock) $stable({A1,A2}) |-> $stable(X)
    );
endmodule