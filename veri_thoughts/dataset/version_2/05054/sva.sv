module PPgen_sva (
    input logic clk,
    input logic Single,
    input logic Yi,
    input logic Double,
    input logic Negate,
    input logic Yi_m1,
    input logic PPi
);

    // PPi must match the implemented combinational equation.
    check_ppi_matches_logic: assert property (
        @(posedge clk)
        PPi == (((Yi & Single) | (Yi_m1 & Double)) ^ Negate)
    );

    // With no active partial-product terms and no negate, PPi must be low.
    check_inactive_terms_no_negate: assert property (
        @(posedge clk)
        ((((Yi & Single) | (Yi_m1 & Double)) == 1'b0) && (Negate == 1'b0)) |-> (PPi == 1'b0)
    );

    // With no active partial-product terms and negate asserted, PPi must be high.
    check_inactive_terms_with_negate: assert property (
        @(posedge clk)
        ((((Yi & Single) | (Yi_m1 & Double)) == 1'b0) && (Negate == 1'b1)) |-> (PPi == 1'b1)
    );

    // With any active partial-product term and no negate, PPi must be high.
    check_active_term_no_negate: assert property (
        @(posedge clk)
        ((((Yi & Single) | (Yi_m1 & Double)) == 1'b1) && (Negate == 1'b0)) |-> (PPi == 1'b1)
    );

    // With any active partial-product term and negate asserted, PPi must be low.
    check_active_term_with_negate: assert property (
        @(posedge clk)
        ((((Yi & Single) | (Yi_m1 & Double)) == 1'b1) && (Negate == 1'b1)) |-> (PPi == 1'b0)
    );

endmodule