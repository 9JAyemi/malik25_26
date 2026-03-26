module combinational_circuit_sva (
    input logic clk,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic B2,
    input logic X
);

    // X must always match the RTL mux expression.
    check_output_matches_rtl_expression: assert property (
        @(posedge clk)
        X === ((A1 == 1'b1) ? B1 : (((A2 == 1'b1) && (A3 == 1'b0)) ? B2 : B1))
    );

    // A1 high selects B1 regardless of A2 and A3.
    check_a1_selects_b1: assert property (
        @(posedge clk)
        (A1 === 1'b1) |-> (X === B1)
    );

    // With A1 low, A2 high, and A3 low, X selects B2.
    check_secondary_condition_selects_b2: assert property (
        @(posedge clk)
        ((A1 === 1'b0) && (A2 === 1'b1) && (A3 === 1'b0)) |-> (X === B2)
    );

    // With A1 low and the secondary condition false, X selects B1.
    check_default_path_selects_b1: assert property (
        @(posedge clk)
        ((A1 === 1'b0) && ((A2 === 1'b0) || (A3 === 1'b1))) |-> (X === B1)
    );

    // A1 has priority over the secondary select condition.
    check_a1_priority_over_secondary_path: assert property (
        @(posedge clk)
        ((A1 === 1'b1) && (A2 === 1'b1) && (A3 === 1'b0)) |-> (X === B1)
    );

endmodule