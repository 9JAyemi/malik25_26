module sky130_fd_sc_ls__a311o_sva (
    input logic X,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic C1
);
    // No clock/reset in DUT; combinational logic. Sample on any port edge.
    // Event: any edge on ports to evaluate combinational relationships.
    // Core function: X == (A1 & A2 & A3) | B1 | C1
    check_function_equivalence: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge A3 or negedge A3
          or posedge B1 or negedge B1 or posedge C1 or negedge C1 or posedge X or negedge X)
        X == ((A1 && A2 && A3) || B1 || C1)
    );

    // B1 high forces X high in the same cycle.
    check_b1_forces_x: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge A3 or negedge A3
          or posedge B1 or negedge B1 or posedge C1 or negedge C1 or posedge X or negedge X)
        B1 |=> (X == 1'b1)
    );

    // C1 high forces X high in the same cycle.
    check_c1_forces_x: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge A3 or negedge A3
          or posedge B1 or negedge B1 or posedge C1 or negedge C1 or posedge X or negedge X)
        C1 |=> (X == 1'b1)
    );

    // A1&A2&A3 high forces X high in the same cycle.
    check_and_term_forces_x: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge A3 or negedge A3
          or posedge B1 or negedge B1 or posedge C1 or negedge C1 or posedge X or negedge X)
        (A1 && A2 && A3) |=> (X == 1'b1)
    );

    // With B1==0 and C1==0, X equals A1&A2&A3.
    check_bc_zero_passes_and: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge A3 or negedge A3
          or posedge B1 or negedge B1 or posedge C1 or negedge C1 or posedge X or negedge X)
        (B1 == 1'b0 && C1 == 1'b0) |=> (X == (A1 && A2 && A3))
    );

    // With B1==0 and C1==0, any A low makes X low.
    check_bc_zero_any_a_low_makes_x_low: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge A3 or negedge A3
          or posedge B1 or negedge B1 or posedge C1 or negedge C1 or posedge X or negedge X)
        (B1 == 1'b0 && C1 == 1'b0 && (!A1 || !A2 || !A3)) |=> (X == 1'b0)
    );

    // If X is high while B1==0 and C1==0, then all A's must be high.
    check_x_high_bc_zero_requires_all_a_high: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge A3 or negedge A3
          or posedge B1 or negedge B1 or posedge C1 or negedge C1 or posedge X or negedge X)
        (X == 1'b1 && B1 == 1'b0 && C1 == 1'b0) |=> (A1 && A2 && A3)
    );

    // X high implies at least one product/sum term is true.
    check_x_high_implies_some_term_true: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge A3 or negedge A3
          or posedge B1 or negedge B1 or posedge C1 or negedge C1 or posedge X or negedge X)
        (X == 1'b1) |=> (B1 || C1 || (A1 && A2 && A3))
    );

    // X low implies all terms are false.
    check_x_low_implies_all_terms_false: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge A3 or negedge A3
          or posedge B1 or negedge B1 or posedge C1 or negedge C1 or posedge X or negedge X)
        (X == 1'b0) |=> ((B1 == 1'b0) && (C1 == 1'b0) && !(A1 && A2 && A3))
    );

    // All inputs low force X low.
    check_all_inputs_low_force_x_low: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge A3 or negedge A3
          or posedge B1 or negedge B1 or posedge C1 or negedge C1 or posedge X or negedge X)
        (!A1 && !A2 && !A3 && !B1 && !C1) |=> (X == 1'b0)
    );
endmodule