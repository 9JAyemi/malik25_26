module custom_module_sva (
    input logic clk,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic Vdd,
    input logic Gnd,
    input logic X
);

    // DUT is combinational; clk is only used to sample assertions.

    // X matches the combinational function implemented by the RTL.
    check_output_function: assert property (
        @(posedge clk) X == (Gnd | (Vdd & ~B1 & (A1 | A2)))
    );

    // Gnd feeds the OR leg of the final stage and forces X high.
    check_gnd_forces_x_high: assert property (
        @(posedge clk) Gnd |-> X
    );

    // With both Gnd and Vdd low, the final output must be low.
    check_no_vdd_and_no_gnd_forces_x_low: assert property (
        @(posedge clk) (~Gnd & ~Vdd) |-> ~X
    );

    // With Gnd low, a high B1 blocks the NOR chain and forces X low.
    check_b1_high_blocks_output: assert property (
        @(posedge clk) (Vdd & ~Gnd & B1) |-> ~X
    );

    // With Gnd low and B1 low, X reduces to the OR of A1 and A2 when powered.
    check_b1_low_passes_a_or: assert property (
        @(posedge clk) (Vdd & ~Gnd & ~B1) |-> (X == (A1 | A2))
    );

    // With Gnd low and both A inputs low, the NOR chain must drive X low.
    check_both_a_low_force_x_low: assert property (
        @(posedge clk) (Vdd & ~Gnd & ~A1 & ~A2) |-> ~X
    );

endmodule