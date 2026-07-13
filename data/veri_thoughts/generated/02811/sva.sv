module or3_circuit_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic X
);
    ///// Combinational OR behavior /////
    // X equals the 3-input OR of A, B, and C.
    check_or_function: assert property (
        @(posedge A or posedge B or posedge C or negedge A or negedge B or negedge C)
            disable iff (1'b0)
            (X === (A | B | C))
    );

    // If any input is 1, X must be 1.
    check_any_input_one_implies_X_one: assert property (
        @(posedge A or posedge B or posedge C or negedge A or negedge B or negedge C)
            disable iff (1'b0)
            ((A === 1'b1) || (B === 1'b1) || (C === 1'b1)) |-> (X === 1'b1)
    );

    // If X is 0, all inputs must be 0.
    check_X_zero_implies_all_zero: assert property (
        @(posedge A or posedge B or posedge C or negedge A or negedge B or negedge C)
            disable iff (1'b0)
            (X === 1'b0) |-> ((A === 1'b0) && (B === 1'b0) && (C === 1'b0))
    );

    // A high implies X high.
    check_A_high_sets_X: assert property (
        @(posedge A or posedge B or posedge C or negedge A or negedge B or negedge C)
            disable iff (1'b0)
            (A === 1'b1) |-> (X === 1'b1)
    );

    // B high implies X high.
    check_B_high_sets_X: assert property (
        @(posedge A or posedge B or posedge C or negedge A or negedge B or negedge C)
            disable iff (1'b0)
            (B === 1'b1) |-> (X === 1'b1)
    );

    // C high implies X high.
    check_C_high_sets_X: assert property (
        @(posedge A or posedge B or posedge C or negedge A or negedge B or negedge C)
            disable iff (1'b0)
            (C === 1'b1) |-> (X === 1'b1)
    );

    // If inputs are stable, X remains stable.
    check_stability_when_inputs_stable: assert property (
        @(posedge A or posedge B or posedge C or negedge A or negedge B or negedge C)
            disable iff (1'b0)
            ($stable(A) && $stable(B) && $stable(C)) |-> $stable(X)
    );

    // From all-zero inputs, a rise on A (only) raises X.
    check_A_rise_from_all_zero_raises_X: assert property (
        @(posedge A or posedge B or posedge C or negedge A or negedge B or negedge C)
            disable iff (1'b0)
            ($past(A === 1'b0) && $past(B === 1'b0) && $past(C === 1'b0) &&
             (A === 1'b1) && (B === 1'b0) && (C === 1'b0)) |-> ($past(X === 1'b0) && (X === 1'b1))
    );

    // From only A=1 (others 0), a fall on A lowers X.
    check_A_fall_to_all_zero_lowers_X: assert property (
        @(posedge A or posedge B or posedge C or negedge A or negedge B or negedge C)
            disable iff (1'b0)
            ($past(A === 1'b1) && $past(B === 1'b0) && $past(C === 1'b0) &&
             (A === 1'b0) && (B === 1'b0) && (C === 1'b0)) |-> ($past(X === 1'b1) && (X === 1'b0))
    );
endmodule