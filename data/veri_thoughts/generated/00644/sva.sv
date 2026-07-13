module sky130_fd_sc_ls__o32a_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic B2
);
    wire a_or = (A1 | A2 | A3);
    wire b_or = (B1 | B2);

    // Output equals (A1|A2|A3) & (B1|B2).
    check_functional_equivalence: assert property (
        @(posedge clk) X == (a_or & b_or)
    );

    // Both B inputs low force X low.
    check_zero_when_b_group_zero: assert property (
        @(posedge clk) (B1 == 1'b0 && B2 == 1'b0) |=> (X == 1'b0)
    );

    // All A inputs low force X low.
    check_zero_when_a_group_zero: assert property (
        @(posedge clk) (A1 == 1'b0 && A2 == 1'b0 && A3 == 1'b0) |=> (X == 1'b0)
    );

    // A1 with any B high sets X high.
    check_a1_with_b_group_sets_x: assert property (
        @(posedge clk) (A1 && b_or) |=> (X == 1'b1)
    );

    // A2 with any B high sets X high.
    check_a2_with_b_group_sets_x: assert property (
        @(posedge clk) (A2 && b_or) |=> (X == 1'b1)
    );

    // A3 with any B high sets X high.
    check_a3_with_b_group_sets_x: assert property (
        @(posedge clk) (A3 && b_or) |=> (X == 1'b1)
    );

    // B1 with any A high sets X high.
    check_b1_with_a_group_sets_x: assert property (
        @(posedge clk) (B1 && a_or) |=> (X == 1'b1)
    );

    // B2 with any A high sets X high.
    check_b2_with_a_group_sets_x: assert property (
        @(posedge clk) (B2 && a_or) |=> (X == 1'b1)
    );

    // X high implies at least one A is high.
    check_x_high_implies_a_group: assert property (
        @(posedge clk) (X == 1'b1) |=> a_or
    );

    // X high implies at least one B is high.
    check_x_high_implies_b_group: assert property (
        @(posedge clk) (X == 1'b1) |=> b_or
    );
endmodule