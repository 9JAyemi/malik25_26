module sky130_fd_sc_hd__or4b_sva (
    input logic X,
    input logic A,
    input logic B,
    input logic C,
    input logic D_N
);
    // X implements A | B | C | ~D_N.
    check_function_equivalence: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D_N or negedge D_N)
        X == (A || B || C || !D_N)
    );

    // A high implies X high.
    check_A_implies_X: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D_N or negedge D_N)
        A |-> X
    );

    // B high implies X high.
    check_B_implies_X: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D_N or negedge D_N)
        B |-> X
    );

    // C high implies X high.
    check_C_implies_X: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D_N or negedge D_N)
        C |-> X
    );

    // D_N low implies X high.
    check_DN_low_implies_X: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D_N or negedge D_N)
        (!D_N) |-> X
    );

    // All inputs low with D_N high implies X low.
    check_all_low_implies_X_low: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D_N or negedge D_N)
        (!A && !B && !C && D_N) |-> (!X)
    );

    // X low implies A,B,C low and D_N high.
    check_X_low_implies_inputs_low: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D_N or negedge D_N)
        (!X) |-> (!A && !B && !C && D_N)
    );

    // With D_N high and B,C low, X mirrors A.
    check_reduce_A_when_DN_high: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D_N or negedge D_N)
        (D_N && !B && !C) |-> (X == A)
    );

    // With D_N high and A,C low, X mirrors B.
    check_reduce_B_when_DN_high: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D_N or negedge D_N)
        (D_N && !A && !C) |-> (X == B)
    );

    // With D_N high and A,B low, X mirrors C.
    check_reduce_C_when_DN_high: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D_N or negedge D_N)
        (D_N && !A && !B) |-> (X == C)
    );

    // With D_N high, X equals A|B|C.
    check_three_input_or_when_DN_high: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D_N or negedge D_N)
        D_N |-> (X == (A || B || C))
    );
endmodule