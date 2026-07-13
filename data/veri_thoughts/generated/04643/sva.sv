module or4bb_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C_N,
    input logic D_N,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB,
    input logic X
);

    // Sampling clock only; RTL has no native clock or reset.

    // X must equal the implemented OR of all input terms.
    check_functional_equivalence: assert property (
        @(posedge clk)
        X == (A | B | ~C_N | ~D_N | VPWR | VGND | VPB | VNB)
    );

    // A or B high forces X high.
    check_a_or_b_drives_high: assert property (
        @(posedge clk)
        (A || B) |-> (X == 1'b1)
    );

    // C_N low is an active-low term that drives X high.
    check_c_n_active_low: assert property (
        @(posedge clk)
        (!C_N) |-> (X == 1'b1)
    );

    // D_N low is an active-low term that drives X high.
    check_d_n_active_low: assert property (
        @(posedge clk)
        (!D_N) |-> (X == 1'b1)
    );

    // Any power or bulk input high forces X high in this RTL.
    check_power_or_bulk_drives_high: assert property (
        @(posedge clk)
        (VPWR || VGND || VPB || VNB) |-> (X == 1'b1)
    );

    // With all OR terms inactive, X must be low.
    check_all_terms_inactive_drives_low: assert property (
        @(posedge clk)
        (!A && !B && C_N && D_N && !VPWR && !VGND && !VPB && !VNB) |-> (X == 1'b0)
    );

    // If X is low, every OR term must be inactive.
    check_x_low_implies_all_terms_inactive: assert property (
        @(posedge clk)
        (X == 1'b0) |-> (!A && !B && C_N && D_N && !VPWR && !VGND && !VPB && !VNB)
    );

endmodule