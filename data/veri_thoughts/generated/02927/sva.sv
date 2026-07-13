module sky130_fd_sc_hs__a31o_wrapper_sva (
    input logic VPWR,
    input logic VGND,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic SEL
);
    // Local expected functions
    logic and4;
    assign and4 = A1 & A2 & A3 & B1;

    ///// Functional equivalence sampled on various input edges /////
    // Y equals selected X/~X on SEL rising edge.
    check_y_function_on_sel_posedge: assert property (
        @(posedge SEL) Y == (SEL ? ~and4 : and4)
    );
    // Y equals selected X/~X on A1 rising edge.
    check_y_function_on_a1_posedge: assert property (
        @(posedge A1) Y == (SEL ? ~and4 : and4)
    );
    // Y equals selected X/~X on A2 rising edge.
    check_y_function_on_a2_posedge: assert property (
        @(posedge A2) Y == (SEL ? ~and4 : and4)
    );
    // Y equals selected X/~X on A3 rising edge.
    check_y_function_on_a3_posedge: assert property (
        @(posedge A3) Y == (SEL ? ~and4 : and4)
    );
    // Y equals selected X/~X on B1 rising edge.
    check_y_function_on_b1_posedge: assert property (
        @(posedge B1) Y == (SEL ? ~and4 : and4)
    );

    ///// Mode-specific checks /////
    // When SEL=0, Y equals AND of A1,A2,A3,B1 (sampled on A1 rising edge).
    check_y_when_sel0: assert property (
        @(posedge A1) (SEL == 1'b0) |-> (Y == and4)
    );
    // When SEL=1, Y equals NOT(AND(A1,A2,A3,B1)) (sampled on A1 rising edge).
    check_y_when_sel1: assert property (
        @(posedge A1) (SEL == 1'b1) |-> (Y == ~and4)
    );

    ///// Implication checks derived from the boolean function /////
    // If SEL=0 and Y=1, then all inputs must be 1 (sampled on A1 rising edge).
    check_sel0_y1_implies_all1: assert property (
        @(posedge A1) (SEL == 1'b0 && Y == 1'b1) |-> (A1 && A2 && A3 && B1)
    );
    // If SEL=1 and Y=0, then all inputs must be 1 (since Y=~AND) (sampled on A1 rising edge).
    check_sel1_y0_implies_all1: assert property (
        @(posedge A1) (SEL == 1'b1 && Y == 1'b0) |-> (A1 && A2 && A3 && B1)
    );
    // If SEL=1 and Y=1, then at least one input must be 0 (sampled on A1 rising edge).
    check_sel1_y1_implies_any0: assert property (
        @(posedge A1) (SEL == 1'b1 && Y == 1'b1) |-> ((~A1) || (~A2) || (~A3) || (~B1))
    );
endmodule