module sky130_fd_sc_hd__a2111oi_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1,
    input logic D1
);

    // Y matches the buffered NOR of B1, C1, D1, and A1&A2.
    check_y_boolean_function: assert property (
        @(posedge clk) disable iff (1'b0)
        Y == ~((A1 & A2) | B1 | C1 | D1)
    );

    // B1 high forces the NOR output low.
    check_b1_forces_y_low: assert property (
        @(posedge clk) disable iff (1'b0)
        B1 |-> !Y
    );

    // C1 high forces the NOR output low.
    check_c1_forces_y_low: assert property (
        @(posedge clk) disable iff (1'b0)
        C1 |-> !Y
    );

    // D1 high forces the NOR output low.
    check_d1_forces_y_low: assert property (
        @(posedge clk) disable iff (1'b0)
        D1 |-> !Y
    );

    // A1 and A2 high together force the NOR output low.
    check_a1_a2_forces_y_low: assert property (
        @(posedge clk) disable iff (1'b0)
        (A1 && A2) |-> !Y
    );

    // With all NOR input terms low, Y must be high.
    check_all_terms_low_gives_y_high: assert property (
        @(posedge clk) disable iff (1'b0)
        (!B1 && !C1 && !D1 && !(A1 && A2)) |-> Y
    );

    // A high Y implies every NOR input term is low.
    check_y_high_implies_all_terms_low: assert property (
        @(posedge clk) disable iff (1'b0)
        Y |-> (!B1 && !C1 && !D1 && !(A1 && A2))
    );

    // A low Y implies at least one NOR input term is high.
    check_y_low_implies_some_term_high: assert property (
        @(posedge clk) disable iff (1'b0)
        !Y |-> (B1 || C1 || D1 || (A1 && A2))
    );

endmodule