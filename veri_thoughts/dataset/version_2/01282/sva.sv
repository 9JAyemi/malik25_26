module my_module_sva (
    input logic CLK,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic VPWR,
    input logic X
);
    // X equals VPWR & B1 & (A1 | A2).
    check_functional_equivalence: assert property (
        @(posedge CLK) X === ((A1 | A2) & B1 & VPWR)
    );

    // If VPWR is 0 then X is 0.
    check_vpwr_low_forces_x_low: assert property (
        @(posedge CLK) (VPWR == 1'b0) |-> (X == 1'b0)
    );

    // If B1 is 0 then X is 0.
    check_b1_low_forces_x_low: assert property (
        @(posedge CLK) (B1 == 1'b0) |-> (X == 1'b0)
    );

    // If A1 and A2 are both 0 then X is 0.
    check_a_inputs_both_low_force_x_low: assert property (
        @(posedge CLK) ((A1 == 1'b0) && (A2 == 1'b0)) |-> (X == 1'b0)
    );

    // If B1 and VPWR are 1 then X equals (A1 | A2).
    check_b1_vpwr_high_x_equals_or: assert property (
        @(posedge CLK) ((B1 == 1'b1) && (VPWR == 1'b1)) |-> (X === (A1 | A2))
    );

    // If (A1 | A2) and VPWR are 1 then X equals B1.
    check_or_high_vpwr_high_x_equals_b1: assert property (
        @(posedge CLK) ((((A1 | A2) == 1'b1)) && (VPWR == 1'b1)) |-> (X === B1)
    );

    // If (A1 | A2) and B1 are 1 then X equals VPWR.
    check_or_high_b1_high_x_equals_vpwr: assert property (
        @(posedge CLK) ((((A1 | A2) == 1'b1)) && (B1 == 1'b1)) |-> (X === VPWR)
    );

    // If all terms are 1 then X is 1.
    check_all_terms_high_imply_x_high: assert property (
        @(posedge CLK) ((VPWR == 1'b1) && (B1 == 1'b1) && ((A1 == 1'b1) || (A2 == 1'b1))) |-> (X == 1'b1)
    );

    // If X is 1 then VPWR=1, B1=1, and (A1|A2)=1.
    check_x_high_requires_terms_high: assert property (
        @(posedge CLK) (X == 1'b1) |-> ((VPWR == 1'b1) && (B1 == 1'b1) && ((A1 == 1'b1) || (A2 == 1'b1)))
    );

    // With B1=1, VPWR=1, A2=0 stable, a rising A1 causes a rising X.
    check_a1_rise_reflects_in_x_when_a2_0: assert property (
        @(posedge CLK)
            ($rose(A1) && (A2 == 1'b0) && (B1 == 1'b1) && (VPWR == 1'b1) &&
             $past(A2 == 1'b0) && $past(B1 == 1'b1) && $past(VPWR == 1'b1))
            |-> $rose(X)
    );

    // With B1=1, VPWR=1, A1=0 stable, a rising A2 causes a rising X.
    check_a2_rise_reflects_in_x_when_a1_0: assert property (
        @(posedge CLK)
            ($rose(A2) && (A1 == 1'b0) && (B1 == 1'b1) && (VPWR == 1'b1) &&
             $past(A1 == 1'b0) && $past(B1 == 1'b1) && $past(VPWR == 1'b1))
            |-> $rose(X)
    );

    // With B1=1, VPWR=1, A2=0 stable, a falling A1 causes a falling X.
    check_a1_fall_reflects_in_x_when_a2_0: assert property (
        @(posedge CLK)
            ($fell(A1) && (A2 == 1'b0) && (B1 == 1'b1) && (VPWR == 1'b1) &&
             $past(A2 == 1'b0) && $past(B1 == 1'b1) && $past(VPWR == 1'b1))
            |-> $fell(X)
    );

    // With B1=1, VPWR=1, A1=0 stable, a falling A2 causes a falling X.
    check_a2_fall_reflects_in_x_when_a1_0: assert property (
        @(posedge CLK)
            ($fell(A2) && (A1 == 1'b0) && (B1 == 1'b1) && (VPWR == 1'b1) &&
             $past(A1 == 1'b0) && $past(B1 == 1'b1) && $past(VPWR == 1'b1))
            |-> $fell(X)
    );
endmodule