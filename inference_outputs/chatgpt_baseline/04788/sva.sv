module sky130_fd_sc_lp__o31ai_sva (
    input logic clk,
    input logic Y,
    input logic VGND,
    input logic VPB,
    input logic VNB,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1
);

    // Y implements ~(B1 & (A1 | A2 | A3)).
    check_functional_equation: assert property (
        @(posedge clk) disable iff (1'b0)
        Y == ~(B1 & (A1 | A2 | A3))
    );

    // B1 low forces the NAND output high.
    check_b1_low_forces_y_high: assert property (
        @(posedge clk) disable iff (1'b0)
        !B1 |-> Y
    );

    // All A inputs low force the OR term low and Y high.
    check_all_a_low_forces_y_high: assert property (
        @(posedge clk) disable iff (1'b0)
        !(A1 | A2 | A3) |-> Y
    );

    // A1 high with B1 high forces Y low.
    check_a1_and_b1_force_y_low: assert property (
        @(posedge clk) disable iff (1'b0)
        (A1 && B1) |-> !Y
    );

    // A2 high with B1 high forces Y low.
    check_a2_and_b1_force_y_low: assert property (
        @(posedge clk) disable iff (1'b0)
        (A2 && B1) |-> !Y
    );

    // A3 high with B1 high forces Y low.
    check_a3_and_b1_force_y_low: assert property (
        @(posedge clk) disable iff (1'b0)
        (A3 && B1) |-> !Y
    );

    // Y low requires B1 high and at least one A input high.
    check_y_low_requires_b1_and_any_a: assert property (
        @(posedge clk) disable iff (1'b0)
        !Y |-> (B1 && (A1 | A2 | A3))
    );

    // Y high while B1 is high requires all A inputs low.
    check_y_high_with_b1_requires_all_a_low: assert property (
        @(posedge clk) disable iff (1'b0)
        (Y && B1) |-> !(A1 | A2 | A3)
    );

endmodule