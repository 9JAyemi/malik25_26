module nand2_en_sva (
    input logic clk,
    input logic Z,
    input logic A,
    input logic B,
    input logic EN
);

    // Z matches the implemented combinational equation.
    check_z_matches_implemented_equation: assert property (
        @(posedge clk) Z == ((~(A & B)) & EN)
    );

    // EN low forces Z low.
    check_en_low_forces_z_low: assert property (
        @(posedge clk) !EN |-> !Z
    );

    // A and B high force Z low.
    check_ab_high_forces_z_low: assert property (
        @(posedge clk) (A && B) |-> !Z
    );

    // EN high with A low forces Z high.
    check_en_high_a_low_forces_z_high: assert property (
        @(posedge clk) (EN && !A) |-> Z
    );

    // EN high with B low forces Z high.
    check_en_high_b_low_forces_z_high: assert property (
        @(posedge clk) (EN && !B) |-> Z
    );

    // Z high requires EN high and at least one input low.
    check_z_high_requires_en_and_one_input_low: assert property (
        @(posedge clk) Z |-> (EN && ((!A) || (!B)))
    );

endmodule