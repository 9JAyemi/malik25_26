module nand2_en_sva (
    input logic clk,
    input logic Z,
    input logic A,
    input logic B,
    input logic EN
);

// Z must match the RTL combinational equation.
    check_functional_equivalence: assert property (
        @(posedge clk) Z == ((~(A & B)) & ~(~(A & B) & EN))
    );

// EN low forces Z low.
    check_en_low_forces_z_low: assert property (
        @(posedge clk) !EN |-> (Z == 1'b0)
    );

// A and B high with EN high drive Z high.
    check_ab_high_with_en_high_drives_z_high: assert property (
        @(posedge clk) (A && B && EN) |-> (Z == 1'b1)
    );

// A low forces Z low.
    check_a_low_forces_z_low: assert property (
        @(posedge clk) !A |-> (Z == 1'b0)
    );

// B low forces Z low.
    check_b_low_forces_z_low: assert property (
        @(posedge clk) !B |-> (Z == 1'b0)
    );

// With EN high, Z equals A & B.
    check_en_high_reduces_to_and: assert property (
        @(posedge clk) EN |-> (Z == (A & B))
    );

// With EN high, a high Z requires A and B high.
    check_en_high_and_z_high_requires_ab_high: assert property (
        @(posedge clk) (EN && Z) |-> (A && B)
    );

endmodule
