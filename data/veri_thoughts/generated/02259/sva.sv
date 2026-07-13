module sky130_fd_sc_lp__o31a_sva (
    input logic X,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1
);
    // Combinational cell with no clock/reset; use global clock for sampling.

    // X matches the RTL expression for all inputs.
    check_full_functional_equivalence: assert property (
        @(posedge $global_clock)
            X == ( B1
                   ? ~((A1 == A2) ? A3 : ~A3)
                   : ( (((A1 == 1'b1) && (A2 == 1'b0)) ? 1'b1 : 1'b0)    // X1
                     | (((A1 == 1'b0) && (A2 == 1'b1)) ? 1'b0 : 1'b1)    // X2
                     | ((A1 == A2) ? A3 : ~A3) )                         // X3
                 )
    );

    // When B1 is HIGH and A1==A2, X is the inversion of A3.
    check_b1_high_equal_case_inverts_a3: assert property (
        @(posedge $global_clock) (B1 && (A1 == A2)) |-> (X == ~A3)
    );

    // When B1 is HIGH and A1!=A2, X equals A3.
    check_b1_high_unequal_case_passes_a3: assert property (
        @(posedge $global_clock) (B1 && (A1 != A2)) |-> (X == A3)
    );

    // When B1 is LOW and A1==1, X is forced HIGH.
    check_b1_low_a1_high_forces_one: assert property (
        @(posedge $global_clock) (!B1 && (A1 == 1'b1)) |-> (X == 1'b1)
    );

    // When B1 is LOW and A2==0, X is forced HIGH.
    check_b1_low_a2_low_forces_one: assert property (
        @(posedge $global_clock) (!B1 && (A2 == 1'b0)) |-> (X == 1'b1)
    );

    // When B1 is LOW and (A1,A2)=(0,1), X equals ~A3.
    check_b1_low_a1_0_a2_1_depends_on_a3: assert property (
        @(posedge $global_clock) (!B1 && (A1 == 1'b0) && (A2 == 1'b1)) |-> (X == ~A3)
    );

    // For B1 LOW, X matches the OR of X1, X2, and X3 per RTL.
    check_b1_low_expression_equivalence: assert property (
        @(posedge $global_clock)
            (!B1) |-> ( X == ( (((A1 == 1'b1) && (A2 == 1'b0)) ? 1'b1 : 1'b0)
                               | (((A1 == 1'b0) && (A2 == 1'b1)) ? 1'b0 : 1'b1)
                               | ((A1 == A2) ? A3 : ~A3) ) )
    );

    // For B1 HIGH, X equals the inversion of X3 per RTL.
    check_b1_high_expression_equivalence: assert property (
        @(posedge $global_clock)
            (B1) |-> ( X == ~((A1 == A2) ? A3 : ~A3) )
    );

    // When B1 is LOW and (A1,A2)=(0,0), X is 1.
    check_b1_low_a1a2_00_forces_one: assert property (
        @(posedge $global_clock) (!B1 && (A1 == 1'b0) && (A2 == 1'b0)) |-> (X == 1'b1)
    );

    // When B1 is LOW and (A1,A2)=(1,1), X is 1.
    check_b1_low_a1a2_11_forces_one: assert property (
        @(posedge $global_clock) (!B1 && (A1 == 1'b1) && (A2 == 1'b1)) |-> (X == 1'b1)
    );
endmodule