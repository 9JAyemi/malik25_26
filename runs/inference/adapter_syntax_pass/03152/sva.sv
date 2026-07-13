module nand2_en_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic EN,
    input logic Z
);

    // Z must match the implemented combinational function.
    check_output_function: assert property (
        @(posedge clk) Z == ((~(A & B)) & EN)
    );

    // EN low must force Z low.
    check_en_low_forces_low: assert property (
        @(posedge clk) !EN |-> !Z
    );

    // A and B high together must force Z low.
    check_ab_high_forces_low: assert property (
        @(posedge clk) (A && B) |-> !Z
    );

    // EN high with A low must force Z low.
    check_en_high_a_low_forces_low: assert property (
        @(posedge clk) (EN && !A) |-> !Z
    );

    // EN high with B low must force Z low.
    check_en_high_b_low_forces_low: assert property (
        @(posedge clk) (EN && !B) |-> !Z
    );

    // EN high with A and B low must drive Z high.
    check_en_high_ab_low_drives_high: assert property (
        @(posedge clk) (EN && !A && !B) |-> Z
    );

    // EN high with A and B high must drive Z low.
    check_en_high_ab_high_drives_low: assert property (
        @(posedge clk) (EN && A && B) |-> !Z
    );

endmodule