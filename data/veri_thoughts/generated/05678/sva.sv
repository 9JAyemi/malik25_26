module module_top_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1,
    input logic D1,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);

    // X matches the implemented OR-of-ANDs function.
    check_x_matches_logic_function: assert property (
        @(posedge clk)
        X == ((A1 & A2) | (B1 & C1) | (D1 & VNB))
    );

    // A1 and A2 high forces X high.
    check_x_set_by_a1_a2: assert property (
        @(posedge clk)
        ((A1 & A2) == 1'b1) |-> (X == 1'b1)
    );

    // B1 and C1 high forces X high.
    check_x_set_by_b1_c1: assert property (
        @(posedge clk)
        ((B1 & C1) == 1'b1) |-> (X == 1'b1)
    );

    // D1 and VNB high forces X high.
    check_x_set_by_d1_vnb: assert property (
        @(posedge clk)
        ((D1 & VNB) == 1'b1) |-> (X == 1'b1)
    );

    // X is low when all three product terms are low.
    check_x_low_when_no_term_is_true: assert property (
        @(posedge clk)
        (((A1 & A2) == 1'b0) && ((B1 & C1) == 1'b0) && ((D1 & VNB) == 1'b0)) |-> (X == 1'b0)
    );

    // X high implies at least one product term is high.
    check_x_high_implies_some_term_true: assert property (
        @(posedge clk)
        (X == 1'b1) |-> (((A1 & A2) == 1'b1) || ((B1 & C1) == 1'b1) || ((D1 & VNB) == 1'b1))
    );

    // If the used logic inputs are stable, X stays stable.
    check_x_stable_when_used_inputs_stable: assert property (
        @(posedge clk)
        (!$initstate && $stable({A1, A2, B1, C1, D1, VNB})) |-> $stable(X)
    );

    // Changing only VPWR, VGND, or VPB does not change X.
    check_unused_power_pins_do_not_change_x: assert property (
        @(posedge clk)
        (!$initstate &&
         ($changed(VPWR) || $changed(VGND) || $changed(VPB)) &&
         $stable({A1, A2, B1, C1, D1, VNB})) |-> $stable(X)
    );

endmodule