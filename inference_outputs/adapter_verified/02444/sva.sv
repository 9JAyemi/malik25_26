module my_buffer_sva (
    input logic clk,
    input logic A,
    input logic Z,
    input logic TE_B,
    input logic VPB,
    input logic VPWR,
    input logic VGND,
    input logic VNB
);

// Z must match the RTL mux equation.
    check_mux_equation: assert property (
        @(posedge clk) Z == (TE_B ? A : 1'b0)
    );

// When TE_B is low, Z must be forced low.
    check_te_b_low_forces_z_low: assert property (
        @(posedge clk) !TE_B |-> (Z == 1'b0)
    );

// When TE_B is high, Z must follow A.
    check_te_b_high_passes_a: assert property (
        @(posedge clk) TE_B |-> (Z == A)
    );

// A rising edge on TE_B must drive Z high.
    check_te_b_rise_sets_z: assert property (
        @(posedge clk) $rose(TE_B) |-> (Z == 1'b1)
    );

// A falling edge on TE_B must drive Z low.
    check_te_b_fall_clears_z: assert property (
        @(posedge clk) $fell(TE_B) |-> (Z == 1'b0)
    );

// A rising edge on A must be reflected on Z when TE_B is high.
    check_a_rise_sets_z_when_te_b_high: assert property (
        @(posedge clk) TE_B && $rose(A) |-> (Z == 1'b1)
    );

// A falling edge on A must be reflected on Z when TE_B is high.
    check_a_fall_clears_z_when_te_b_high: assert property (
        @(posedge clk) TE_B && $fell(A) |-> (Z == 1'b0)
    );

endmodule
