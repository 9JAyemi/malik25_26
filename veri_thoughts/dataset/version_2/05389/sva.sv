module sky130_fd_sc_ls__a32oi_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic B2
);

    // Sample this combinational cell on an external clk; no reset exists in the RTL.

    // Y must implement ~(A1&A2&A3 | B1&B2).
    check_output_equation: assert property (
        @(posedge clk) Y == ~((A1 & A2 & A3) | (B1 & B2))
    );

    // A true 3-input A product term forces Y low.
    check_a_product_forces_low: assert property (
        @(posedge clk) (A1 & A2 & A3) |-> (Y == 1'b0)
    );

    // A true 2-input B product term forces Y low.
    check_b_product_forces_low: assert property (
        @(posedge clk) (B1 & B2) |-> (Y == 1'b0)
    );

    // With both product terms inactive, Y must be high.
    check_no_product_terms_drive_high: assert property (
        @(posedge clk) (!(A1 & A2 & A3) && !(B1 & B2)) |-> (Y == 1'b1)
    );

    // A high Y means neither product term is active.
    check_high_output_decode: assert property (
        @(posedge clk) (Y == 1'b1) |-> (!(A1 & A2 & A3) && !(B1 & B2))
    );

    // A low Y means at least one product term is active.
    check_low_output_decode: assert property (
        @(posedge clk) (Y == 1'b0) |-> ((A1 & A2 & A3) || (B1 & B2))
    );

    // If all inputs are stable across samples, Y must remain stable.
    check_stable_inputs_keep_output_stable: assert property (
        @(posedge clk) $stable({A1, A2, A3, B1, B2}) |-> $stable(Y)
    );

endmodule