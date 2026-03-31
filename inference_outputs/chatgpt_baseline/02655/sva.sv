module or4_2_custom_sva (
    input logic X,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB,
    input logic or_output
);
    // Note: No clock/reset in DUT; sample on any edge of inputs/outputs.

    // X equals the OR of A,B,C,D.
    check_top_or_function: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D or posedge X or negedge X or posedge or_output or negedge or_output)
        (X == (A | B | C | D))
    );

    // Internal or_output equals the OR of A,B,C,D.
    check_internal_or_function: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D or posedge X or negedge X or posedge or_output or negedge or_output)
        (or_output == (A | B | C | D))
    );

    // X passes through or_output.
    check_pass_through_or_output: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D or posedge X or negedge X or posedge or_output or negedge or_output)
        (X == or_output)
    );

    // When all inputs are 0, X must be 0.
    check_zero_inputs_zero_X: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D or posedge X or negedge X or posedge or_output or negedge or_output)
        ((!A && !B && !C && !D) |-> (X == 1'b0))
    );

    // When any input is 1, X must be 1.
    check_any_input_sets_X: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D or posedge X or negedge X or posedge or_output or negedge or_output)
        ((A || B || C || D) |-> (X == 1'b1))
    );

    // If X is 1, at least one input must be 1.
    check_X_high_implies_any_input_high: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D or posedge X or negedge X or posedge or_output or negedge or_output)
        (X |-> (A || B || C || D))
    );

    // If or_output is 1, at least one input must be 1.
    check_or_output_high_implies_any_input_high: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D or posedge X or negedge X or posedge or_output or negedge or_output)
        (or_output |-> (A || B || C || D))
    );

    // When all inputs are 0, or_output must be 0.
    check_zero_inputs_zero_or_output: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D or posedge X or negedge X or posedge or_output or negedge or_output)
        ((!A && !B && !C && !D) |-> (or_output == 1'b0))
    );

    // If A is 1, X must be 1.
    check_A_sets_X: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D or posedge X or negedge X or posedge or_output or negedge or_output)
        (A |-> (X == 1'b1))
    );

    // If B is 1, X must be 1.
    check_B_sets_X: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D or posedge X or negedge X or posedge or_output or negedge or_output)
        (B |-> (X == 1'b1))
    );

endmodule