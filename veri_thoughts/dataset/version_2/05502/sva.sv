module signal_converter_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic C1
);

    // No reset exists in the RTL, so assertions are always active.

    // X must match the exact RTL sum-of-products expression.
    check_output_matches_rtl_sum_of_products: assert property (
        @(posedge clk) disable iff (1'b0)
        X == (
            (A1 & A2 & A3) |
            (A1 & A2 & B1) |
            (A1 & A2 & C1) |
            (A1 & A3 & B1) |
            (A1 & A3 & C1) |
            (A1 & B1 & C1) |
            (A2 & A3 & B1) |
            (A2 & A3 & C1) |
            (A2 & B1 & C1) |
            (A3 & B1 & C1)
        )
    );

    // Three or more asserted inputs must drive X high.
    check_three_or_more_high_drive_x_high: assert property (
        @(posedge clk) disable iff (1'b0)
        (
            (A1 ? 3'd1 : 3'd0) +
            (A2 ? 3'd1 : 3'd0) +
            (A3 ? 3'd1 : 3'd0) +
            (B1 ? 3'd1 : 3'd0) +
            (C1 ? 3'd1 : 3'd0)
        ) >= 3'd3 |-> X
    );

    // Fewer than three asserted inputs must drive X low.
    check_fewer_than_three_high_drive_x_low: assert property (
        @(posedge clk) disable iff (1'b0)
        (
            (A1 ? 3'd1 : 3'd0) +
            (A2 ? 3'd1 : 3'd0) +
            (A3 ? 3'd1 : 3'd0) +
            (B1 ? 3'd1 : 3'd0) +
            (C1 ? 3'd1 : 3'd0)
        ) < 3'd3 |-> !X
    );

    // All inputs low must drive X low.
    check_all_low_case: assert property (
        @(posedge clk) disable iff (1'b0)
        (!A1 && !A2 && !A3 && !B1 && !C1) |-> !X
    );

    // All inputs high must drive X high.
    check_all_high_case: assert property (
        @(posedge clk) disable iff (1'b0)
        (A1 && A2 && A3 && B1 && C1) |-> X
    );

    // The A1/A2/A3 product term must force X high.
    check_selected_three_input_term_a1a2a3: assert property (
        @(posedge clk) disable iff (1'b0)
        (A1 && A2 && A3) |-> X
    );

    // The A1/B1/C1 product term must force X high.
    check_selected_three_input_term_a1b1c1: assert property (
        @(posedge clk) disable iff (1'b0)
        (A1 && B1 && C1) |-> X
    );

    // Exactly two asserted inputs are not enough to drive X high.
    check_exact_two_input_case_a1a2: assert property (
        @(posedge clk) disable iff (1'b0)
        (A1 && A2 && !A3 && !B1 && !C1) |-> !X
    );

    // Exactly one asserted input is not enough to drive X high.
    check_exact_one_input_case_c1: assert property (
        @(posedge clk) disable iff (1'b0)
        (!A1 && !A2 && !A3 && !B1 && C1) |-> !X
    );

    // Any representative four-high input case must drive X high.
    check_exact_four_input_case_a1a2a3b1: assert property (
        @(posedge clk) disable iff (1'b0)
        (A1 && A2 && A3 && B1 && !C1) |-> X
    );

endmodule