module nand2_en_assertions (
    input logic clk,
    input logic Z,
    input logic A,
    input logic B,
    input logic EN
);

    // Z must match the implemented gate-level RTL expression.
    check_output_matches_rtl: assert property (
        @(posedge clk) Z == ((~((~(A & B)) & EN)) & (A & B))
    );

    // When both inputs are high, Z must be high regardless of EN.
    check_ab_high_drive_z_high: assert property (
        @(posedge clk) (A & B) |-> Z
    );

    // Z can only be high when both inputs are high.
    check_z_high_requires_ab_high: assert property (
        @(posedge clk) Z |-> (A & B)
    );

    // If either input is low, Z must be low regardless of EN.
    check_any_low_drives_z_low: assert property (
        @(posedge clk) ((!A) || (!B)) |-> (!Z)
    );

endmodule