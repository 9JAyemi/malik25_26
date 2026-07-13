module mux_2to1_power_sva (
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic X,
    input logic VPB,
    input logic VPWR,
    input logic VGND,
    input logic VNB
);
    // When neither select is asserted, X must be 0.
    check_no_select_forces_zero: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge B2 or negedge B2)
        (!A1 && !A2) |-> (X == 1'b0)
    );

    // When A1 is asserted, X must equal B1.
    check_a1_selects_b1: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge B2 or negedge B2)
        A1 |-> (X == B1)
    );

    // When only A2 is asserted, X must equal B2.
    check_a2_selects_b2_when_a1_zero: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge B2 or negedge B2)
        (!A1 && A2) |-> (X == B2)
    );

    // Functional equivalence of X to the boolean expression.
    check_functional_equivalence: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge B2 or negedge B2)
        X == ((A1 && B1) || ((!A1) && A2 && B2))
    );

    // If X is 1, it must come from either A1&B1 or (!A1)&A2&B2.
    check_x_high_requires_valid_path: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge B2 or negedge B2)
        (X == 1'b1) |-> ((A1 && B1) || ((!A1) && A2 && B2))
    );

    // If both data inputs are 0, X must be 0 regardless of selects.
    check_zero_when_both_data_zero: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge B2 or negedge B2)
        (!B1 && !B2) |-> (X == 1'b0)
    );

    // A1=1 and B1=1 must drive X=1.
    check_high_when_a1_and_b1_high: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge B2 or negedge B2)
        (A1 && B1) |-> (X == 1'b1)
    );

    // With A1=0 and A2=1, B2=1 must drive X=1.
    check_high_when_a2_selected_and_b2_high: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge B2 or negedge B2)
        ((!A1) && A2 && B2) |-> (X == 1'b1)
    );
endmodule