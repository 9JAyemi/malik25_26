module seven_to_one_sva (
    input  logic CLK,
    input  logic RESETn,
    input  logic A1,
    input  logic A2,
    input  logic B1,
    input  logic B2,
    input  logic C1,
    input  logic C2,
    input  logic C3,
    input  logic X
);
    // X equals (A1&A2&B1&B2) OR NOT(C1|C2|C3).
    check_function_equivalence: assert property (
        @(posedge CLK) disable iff (!RESETn)
            X == ( (A1 & A2 & B1 & B2) | ~(C1 | C2 | C3) )
    );

    // If all A/B inputs are 1, X must be 1.
    check_X_one_when_all_A_B_high: assert property (
        @(posedge CLK) disable iff (!RESETn)
            (A1 & A2 & B1 & B2) |-> (X == 1'b1)
    );

    // If all C inputs are 0, X must be 1.
    check_X_one_when_all_C_low: assert property (
        @(posedge CLK) disable iff (!RESETn)
            (~(C1 | C2 | C3) == 1'b1) |-> (X == 1'b1)
    );

    // If any C is 1 and not all A/B are 1, X must be 0.
    check_X_zero_when_any_C_high_and_not_all_A_B: assert property (
        @(posedge CLK) disable iff (!RESETn)
            ((C1 | C2 | C3) && ~((A1 & A2 & B1 & B2))) |-> (X == 1'b0)
    );

    // If X is 0, then at least one C is 1 and not all A/B are 1.
    check_X_zero_implies_inputs: assert property (
        @(posedge CLK) disable iff (!RESETn)
            (X == 1'b0) |-> (((C1 | C2 | C3) == 1'b1) && ((A1 & A2 & B1 & B2) == 1'b0))
    );

    // If X is 1, then either all A/B are 1 or all C are 0.
    check_X_one_implies_inputs: assert property (
        @(posedge CLK) disable iff (!RESETn)
            (X == 1'b1) |-> (((A1 & A2 & B1 & B2) == 1'b1) || (~(C1 | C2 | C3) == 1'b1))
    );

    // If (A1&A2&B1&B2) rises and C inputs are stable, X must be 1.
    check_X_one_on_A_group_rise_with_C_stable: assert property (
        @(posedge CLK) disable iff (!RESETn)
            ($rose(A1 & A2 & B1 & B2) && $stable(C1) && $stable(C2) && $stable(C3)) |-> (X == 1'b1)
    );

    // If ~(C1|C2|C3) rises (all C become 0), X must be 1.
    check_X_one_on_all_C_low_rise: assert property (
        @(posedge CLK) disable iff (!RESETn)
            $rose(~(C1 | C2 | C3)) |-> (X == 1'b1)
    );

    // If (C1|C2|C3) rises while all A/B remain not all 1, X must be 0.
    check_X_zero_on_any_C_rise_with_A_group_stable_zero: assert property (
        @(posedge CLK) disable iff (!RESETn)
            ($rose(C1 | C2 | C3) && $stable(A1) && $stable(A2) && $stable(B1) && $stable(B2) && ((A1 & A2 & B1 & B2) == 1'b0)) |-> (X == 1'b0)
    );

    // If all inputs are stable, X must be stable.
    check_output_stable_when_inputs_stable: assert property (
        @(posedge CLK) disable iff (!RESETn)
            ($stable(A1) && $stable(A2) && $stable(B1) && $stable(B2) && $stable(C1) && $stable(C2) && $stable(C3)) |-> $stable(X)
    );
endmodule