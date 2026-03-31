module sky130_fd_sc_lp__a311oi_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic C1
);

    // Y matches the implemented AND-NOR-ORI function.
    check_function_equivalence: assert property (
        @(posedge clk) Y == ~(A1 & A2 & A3 | B1 | C1)
    );

    // B1 high forces the NOR output low.
    check_b1_forces_y_low: assert property (
        @(posedge clk) B1 |-> !Y
    );

    // C1 high forces the NOR output low.
    check_c1_forces_y_low: assert property (
        @(posedge clk) C1 |-> !Y
    );

    // All three A inputs high force the AND term high and Y low.
    check_all_a_high_forces_y_low: assert property (
        @(posedge clk) (A1 & A2 & A3) |-> !Y
    );

    // With B1 and C1 low, Y reduces to the inverted 3-input AND of A1/A2/A3.
    check_bc_low_reduces_to_and3: assert property (
        @(posedge clk) (!B1 && !C1) |-> (Y == ~(A1 & A2 & A3))
    );

    // With B1 and C1 low, Y high means the AND term must be low.
    check_bc_low_y_high_requires_and_term_low: assert property (
        @(posedge clk) (!B1 && !C1 && Y) |-> !(A1 & A2 & A3)
    );

    // With B1 and C1 low, Y low means the AND term must be high.
    check_bc_low_y_low_requires_and_term_high: assert property (
        @(posedge clk) (!B1 && !C1 && !Y) |-> (A1 & A2 & A3)
    );

    // With B1 and C1 low, a high Y implies not all A inputs are high.
    check_bc_low_y_high_implies_not_all_a_high: assert property (
        @(posedge clk) (!B1 && !C1 && Y) |-> !(A1 & A2 & A3)
    );

    // With B1 and C1 low, a low Y implies all A inputs are high.
    check_bc_low_y_low_implies_all_a_high: assert property (
        @(posedge clk) (!B1 && !C1 && !Y) |-> (A1 & A2 & A3)
    );

endmodule