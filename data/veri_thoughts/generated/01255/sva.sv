module six_input_module_sva (
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic C1,
    input logic VPB,
    input logic VPWR,
    input logic VGND,
    input logic VNB,
    input logic Y
);
    // Y equals the RTL boolean function when A1 toggles.
    check_func_eq_on_A1: assert property (
        @(posedge A1) Y == ((A1 & A2 & ~B1 & ~B2) | (~A1 & ~A2 & B1 & B2) | C1)
    );

    // Y equals the RTL boolean function when A2 toggles.
    check_func_eq_on_A2: assert property (
        @(posedge A2) Y == ((A1 & A2 & ~B1 & ~B2) | (~A1 & ~A2 & B1 & B2) | C1)
    );

    // Y equals the RTL boolean function when B1 toggles.
    check_func_eq_on_B1: assert property (
        @(posedge B1) Y == ((A1 & A2 & ~B1 & ~B2) | (~A1 & ~A2 & B1 & B2) | C1)
    );

    // Y equals the RTL boolean function when B2 toggles.
    check_func_eq_on_B2: assert property (
        @(posedge B2) Y == ((A1 & A2 & ~B1 & ~B2) | (~A1 & ~A2 & B1 & B2) | C1)
    );

    // Y equals the RTL boolean function when C1 toggles.
    check_func_eq_on_C1: assert property (
        @(posedge C1) Y == ((A1 & A2 & ~B1 & ~B2) | (~A1 & ~A2 & B1 & B2) | C1)
    );

    // C1 high forces Y high.
    check_c1_dominates_y: assert property (
        @(posedge C1) C1 |-> (Y == 1'b1)
    );

    // A1&A2&~B1&~B2 implies Y high.
    check_aa11_bb00_implies_y1: assert property (
        @(posedge A1) (A1 & A2 & ~B1 & ~B2) |-> (Y == 1'b1)
    );

    // ~A1&~A2&B1&B2 implies Y high.
    check_aa00_bb11_implies_y1: assert property (
        @(posedge B1) (~A1 & ~A2 & B1 & B2) |-> (Y == 1'b1)
    );

    // If no term true and C1 low, Y must be low.
    check_else_case_y0: assert property (
        @(posedge A2) (!C1 && !((A1 & A2 & ~B1 & ~B2) | (~A1 & ~A2 & B1 & B2))) |-> (Y == 1'b0)
    );

    // Any rising edge of Y must be due to the function being true.
    check_y_rise_consistent_with_function: assert property (
        @(posedge Y) ((A1 & A2 & ~B1 & ~B2) | (~A1 & ~A2 & B1 & B2) | C1)
    );
endmodule