module sky130_fd_sc_ms__a222o_1_sva (
    input logic CLK,
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic C1,
    input logic C2
);
    // X equals OR of three 2-input AND terms.
    check_functional_equivalence: assert property (
        @(posedge CLK) X === ((A1 & A2) | (B1 & B2) | (C1 & C2))
    );

    // If A1&A2 are HIGH, X must be HIGH.
    check_high_if_A_pair_high: assert property (
        @(posedge CLK) (A1 & A2) |=> (X == 1'b1)
    );

    // If B1&B2 are HIGH, X must be HIGH.
    check_high_if_B_pair_high: assert property (
        @(posedge CLK) (B1 & B2) |=> (X == 1'b1)
    );

    // If C1&C2 are HIGH, X must be HIGH.
    check_high_if_C_pair_high: assert property (
        @(posedge CLK) (C1 & C2) |=> (X == 1'b1)
    );

    // If no pair is HIGH, X must be LOW.
    check_low_if_all_pairs_low: assert property (
        @(posedge CLK) ((A1 & A2) == 1'b0) && ((B1 & B2) == 1'b0) && ((C1 & C2) == 1'b0) |=> (X == 1'b0)
    );

    // X can be HIGH only if at least one pair is HIGH.
    check_X_high_requires_some_pair_high: assert property (
        @(posedge CLK) (X == 1'b1) |=> ((A1 & A2) || (B1 & B2) || (C1 & C2))
    );

    // X can be LOW only if no pair is HIGH.
    check_X_low_requires_no_pair_high: assert property (
        @(posedge CLK) (X == 1'b0) |=> (((A1 & A2) == 1'b0) && ((B1 & B2) == 1'b0) && ((C1 & C2) == 1'b0))
    );

    // If inputs are stable, X is stable.
    check_stable_when_inputs_stable: assert property (
        @(posedge CLK) $stable({A1,A2,B1,B2,C1,C2}) |=> $stable(X)
    );

    // X changes only when the function of inputs changes.
    check_output_change_implies_function_change: assert property (
        @(posedge CLK) $changed(X) |=> $changed((A1 & A2) | (B1 & B2) | (C1 & C2))
    );

    // Function of inputs changes only when some input changes.
    check_function_change_implies_input_change: assert property (
        @(posedge CLK) $changed((A1 & A2) | (B1 & B2) | (C1 & C2)) |=> $changed({A1,A2,B1,B2,C1,C2})
    );
endmodule