module my_logic_sva (
    input logic CLK,
    input logic RESETn,
    input logic X,
    input logic A1_N,
    input logic A2_N,
    input logic B1,
    input logic B2
);
    // X implements the exact boolean function of the RTL.
    check_function_equivalence: assert property (
        @(posedge CLK) disable iff (!RESETn)
            X == ((A1_N && ~A2_N && B1 && ~B2) || (A2_N && ~A1_N && ~B1 && B2))
    );

    // When both A1_N and A2_N are HIGH, X must be 0.
    check_both_A_high_zero: assert property (
        @(posedge CLK) disable iff (!RESETn)
            (A1_N && A2_N) |-> (X == 1'b0)
    );

    // When both A1_N and A2_N are LOW, X must be 0.
    check_both_A_low_zero: assert property (
        @(posedge CLK) disable iff (!RESETn)
            (~A1_N && ~A2_N) |-> (X == 1'b0)
    );

    // When A1_N=1 and A2_N=0, X equals (B1 & ~B2).
    check_A1_only_mapping: assert property (
        @(posedge CLK) disable iff (!RESETn)
            (A1_N && ~A2_N) |-> (X == (B1 && ~B2))
    );

    // When A1_N=1 and A2_N=0 and (~B1 | B2), X must be 0.
    check_A1_only_else_zero: assert property (
        @(posedge CLK) disable iff (!RESETn)
            (A1_N && ~A2_N && (~B1 || B2)) |-> (X == 1'b0)
    );

    // When A2_N=1 and A1_N=0, X equals (~B1 & B2).
    check_A2_only_mapping: assert property (
        @(posedge CLK) disable iff (!RESETn)
            (~A1_N && A2_N) |-> (X == (~B1 && B2))
    );

    // When A2_N=1 and A1_N=0 and (B1 | ~B2), X must be 0.
    check_A2_only_else_zero: assert property (
        @(posedge CLK) disable iff (!RESETn)
            (A2_N && ~A1_N && (B1 || ~B2)) |-> (X == 1'b0)
    );

    // X high implies A1_N and A2_N differ.
    check_X_implies_A_diff: assert property (
        @(posedge CLK) disable iff (!RESETn)
            (X == 1'b1) |-> (A1_N != A2_N)
    );

    // X high implies B1 and B2 differ.
    check_X_implies_B_diff: assert property (
        @(posedge CLK) disable iff (!RESETn)
            (X == 1'b1) |-> (B1 != B2)
    );

    // If B1 equals B2, X must be 0.
    check_B_equal_implies_zero: assert property (
        @(posedge CLK) disable iff (!RESETn)
            (B1 == B2) |-> (X == 1'b0)
    );
endmodule