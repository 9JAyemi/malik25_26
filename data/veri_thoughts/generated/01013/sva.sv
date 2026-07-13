module sky130_fd_sc_ls__or4_sva (
    input logic CLK,
    input logic X,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic or0_out_X
);
    ///// Functional equivalence /////
    // X equals the OR of A,B,C,D.
    check_or_function_eq: assert property (
        @(posedge CLK) X == (A | B | C | D)
    );

    ///// Internal net and buffer consistency /////
    // Internal OR output equals the OR of A,B,C,D.
    check_internal_or_net_function: assert property (
        @(posedge CLK) or0_out_X == (A | B | C | D)
    );
    // Buffer is non-inverting: X equals internal OR output.
    check_buffer_non_inverting: assert property (
        @(posedge CLK) X == or0_out_X
    );

    ///// Basic truth-table implications /////
    // If all inputs are 0 then X must be 0.
    check_all_zero_drives_zero: assert property (
        @(posedge CLK) (~A & ~B & ~C & ~D) |-> (X == 1'b0)
    );
    // If any input is 1 then X must be 1.
    check_any_one_drives_one: assert property (
        @(posedge CLK) (A | B | C | D) |-> (X == 1'b1)
    );
    // If X is 0 then all inputs must be 0.
    check_zero_output_means_all_zero: assert property (
        @(posedge CLK) (X == 1'b0) |-> (~A & ~B & ~C & ~D)
    );
    // If X is 1 then at least one input is 1.
    check_one_output_means_some_one: assert property (
        @(posedge CLK) (X == 1'b1) |-> (A | B | C | D)
    );

    ///// Temporal consistency /////
    // If inputs are stable across a cycle, X must be stable.
    check_stable_inputs_imply_stable_output: assert property (
        @(posedge CLK) ($stable(A) && $stable(B) && $stable(C) && $stable(D)) |-> $stable(X)
    );
    // X can change across a cycle only if some input changes.
    check_output_change_requires_input_change: assert property (
        @(posedge CLK) $changed(X) |-> ($changed(A) || $changed(B) || $changed(C) || $changed(D))
    );

    ///// Edge-specific behaviors /////
    // A single rising A from all-zero inputs causes X to rise.
    check_single_A_rise_causes_X_rise: assert property (
        @(posedge CLK)
            ($past({A,B,C,D}) == 4'b0000) && ({A,B,C,D} == 4'b1000) |-> $rose(X)
    );
    // A single falling A from one-hot A causes X to fall.
    check_single_A_fall_causes_X_fall: assert property (
        @(posedge CLK)
            ($past({A,B,C,D}) == 4'b1000) && ({A,B,C,D} == 4'b0000) |-> $fell(X)
    );
endmodule