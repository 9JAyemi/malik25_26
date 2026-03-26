module my_nand4_sva (
    input logic clk,
    input logic Y,
    input logic A,
    input logic B,
    input logic C,
    input logic D
);

    // Y must match the 4-input NAND function.
    check_nand_equation: assert property (
        @(posedge clk) (Y === ~(A & B & C & D))
    );

    // All inputs high drives Y low.
    check_all_high_drives_low: assert property (
        @(posedge clk) ((A === 1'b1) && (B === 1'b1) && (C === 1'b1) && (D === 1'b1)) |-> (Y === 1'b0)
    );

    // A low forces Y high.
    check_a_low_forces_high: assert property (
        @(posedge clk) (A === 1'b0) |-> (Y === 1'b1)
    );

    // B low forces Y high.
    check_b_low_forces_high: assert property (
        @(posedge clk) (B === 1'b0) |-> (Y === 1'b1)
    );

    // C low forces Y high.
    check_c_low_forces_high: assert property (
        @(posedge clk) (C === 1'b0) |-> (Y === 1'b1)
    );

    // D low forces Y high.
    check_d_low_forces_high: assert property (
        @(posedge clk) (D === 1'b0) |-> (Y === 1'b1)
    );

endmodule