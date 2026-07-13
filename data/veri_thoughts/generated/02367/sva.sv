module sky130_fd_sc_hd__a311o_sva (
    input logic X,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic C1
);
    // X implements (A1 & A2 & A3) | B1 | C1.
    check_functional_equivalence: assert property (
        @(posedge $global_clock) X === ((A1 & A2 & A3) | B1 | C1)
    );

    // If B1 is HIGH, X must be HIGH.
    check_b1_forces_high: assert property (
        @(posedge $global_clock) (B1 == 1'b1) |-> (X == 1'b1)
    );

    // If C1 is HIGH, X must be HIGH.
    check_c1_forces_high: assert property (
        @(posedge $global_clock) (C1 == 1'b1) |-> (X == 1'b1)
    );

    // If A1&A2&A3 is HIGH, X must be HIGH.
    check_and3_forces_high: assert property (
        @(posedge $global_clock) ((A1 & A2 & A3) == 1'b1) |-> (X == 1'b1)
    );

    // If all OR terms are LOW, X must be LOW.
    check_all_terms_low_implies_x_low: assert property (
        @(posedge $global_clock) ((B1==1'b0) && (C1==1'b0) && ((A1 & A2 & A3)==1'b0)) |-> (X == 1'b0)
    );

    // If X is LOW, all OR terms must be LOW.
    check_x_low_requires_all_terms_low: assert property (
        @(posedge $global_clock) (X == 1'b0) |-> ((B1==1'b0) && (C1==1'b0) && ((A1 & A2 & A3)==1'b0))
    );

    // If X is HIGH and B1,C1 are LOW, then A1&A2&A3 must be HIGH.
    check_x_high_with_bc_low_requires_and3: assert property (
        @(posedge $global_clock) ((X==1'b1) && (B1==1'b0) && (C1==1'b0)) |-> ((A1 & A2 & A3) == 1'b1)
    );

    // If X is HIGH and A1&A2&A3 is LOW, then B1 or C1 must be HIGH.
    check_x_high_with_and3_low_requires_b_or_c: assert property (
        @(posedge $global_clock) ((X==1'b1) && ((A1 & A2 & A3) == 1'b0)) |-> ((B1==1'b1) || (C1==1'b1))
    );

    // When B1 and C1 are LOW, X equals A1&A2&A3.
    check_x_equals_and3_when_bc_low: assert property (
        @(posedge $global_clock) ((B1==1'b0) && (C1==1'b0)) |-> (X === (A1 & A2 & A3))
    );

    // When A1&A2&A3 is LOW, X equals B1|C1.
    check_x_equals_b_or_c_when_and3_low: assert property (
        @(posedge $global_clock) (((A1 & A2 & A3) == 1'b0)) |-> (X === (B1 | C1))
    );
endmodule