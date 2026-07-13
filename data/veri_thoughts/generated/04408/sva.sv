module Problem4_assertions (
    input logic clk,
    input logic A,
    input logic B,
    input logic GTI,
    input logic LTI,
    input logic EQI,
    input logic GTO,
    input logic LTO,
    input logic EQO
);

    // A greater than B drives only GTO high.
    check_gt_case_outputs: assert property (
        @(posedge clk) (A > B) |-> ((GTO == 1'b1) && (LTO == 1'b0) && (EQO == 1'b0))
    );

    // A less than B drives only LTO high.
    check_lt_case_outputs: assert property (
        @(posedge clk) (A < B) |-> ((GTO == 1'b0) && (LTO == 1'b1) && (EQO == 1'b0))
    );

    // Equal inputs pass GTI through to GTO.
    check_eq_case_gto_passthrough: assert property (
        @(posedge clk) (A == B) |-> (GTO == GTI)
    );

    // Equal inputs pass LTI through to LTO.
    check_eq_case_lto_passthrough: assert property (
        @(posedge clk) (A == B) |-> (LTO == LTI)
    );

    // Equal inputs pass EQI through to EQO.
    check_eq_case_eqo_passthrough: assert property (
        @(posedge clk) (A == B) |-> (EQO == EQI)
    );

endmodule