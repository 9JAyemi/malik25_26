module sky130_fd_sc_ls__a2111oi_sva (
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1,
    input logic D1
);
    // Y equals ~(B1 | C1 | D1 | (A1 & A2)).
    check_function_equivalence: assert property (
        @(posedge A1 or posedge A2 or posedge B1 or posedge C1 or posedge D1 or posedge Y)
            Y == ~(B1 | C1 | D1 | (A1 & A2))
    );

    // B1 high forces Y low.
    check_b1_forces_y_low: assert property (
        @(posedge A1 or posedge A2 or posedge B1 or posedge C1 or posedge D1 or posedge Y)
            (B1 == 1'b1) |-> (Y == 1'b0)
    );

    // C1 high forces Y low.
    check_c1_forces_y_low: assert property (
        @(posedge A1 or posedge A2 or posedge B1 or posedge C1 or posedge D1 or posedge Y)
            (C1 == 1'b1) |-> (Y == 1'b0)
    );

    // D1 high forces Y low.
    check_d1_forces_y_low: assert property (
        @(posedge A1 or posedge A2 or posedge B1 or posedge C1 or posedge D1 or posedge Y)
            (D1 == 1'b1) |-> (Y == 1'b0)
    );

    // A1&A2 high forces Y low.
    check_a1a2_forces_y_low: assert property (
        @(posedge A1 or posedge A2 or posedge B1 or posedge C1 or posedge D1 or posedge Y)
            ((A1 & A2) == 1'b1) |-> (Y == 1'b0)
    );

    // All inputs low (including A1&A2==0) makes Y high.
    check_all_zero_make_y_high: assert property (
        @(posedge A1 or posedge A2 or posedge B1 or posedge C1 or posedge D1 or posedge Y)
            ((B1 == 1'b0) && (C1 == 1'b0) && (D1 == 1'b0) && ((A1 & A2) == 1'b0)) |-> (Y == 1'b1)
    );

    // Y high implies B1==0, C1==0, D1==0, and (A1&A2)==0.
    check_y_high_implies_inputs_zero: assert property (
        @(posedge A1 or posedge A2 or posedge B1 or posedge C1 or posedge D1 or posedge Y)
            (Y == 1'b1) |-> ((B1 == 1'b0) && (C1 == 1'b0) && (D1 == 1'b0) && ((A1 & A2) == 1'b0))
    );

    // Y low implies at least one of B1,C1,D1,(A1&A2) is high.
    check_y_low_implies_some_input_one: assert property (
        @(posedge A1 or posedge A2 or posedge B1 or posedge C1 or posedge D1 or posedge Y)
            (Y == 1'b0) |-> (B1 || C1 || D1 || (A1 & A2))
    );
endmodule