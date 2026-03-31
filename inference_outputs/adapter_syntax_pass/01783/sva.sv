module two_bit_adder_sva (
    input logic clk,
    input logic X,
    input logic A1_N,
    input logic A2_N,
    input logic B1,
    input logic B2,
    input logic OUT
);

    // OUT matches the implemented NAND/NOR combinational function.
    check_out_matches_function: assert property (
        @(posedge clk) OUT == ~((~A1_N & ~A2_N) | (B1 & B2))
    );

    // A1_N and A2_N both low force OUT high.
    check_a_term_forces_high: assert property (
        @(posedge clk) (~A1_N & ~A2_N) |-> OUT
    );

    // B1 and B2 both high force OUT high.
    check_b_term_forces_high: assert property (
        @(posedge clk) (B1 & B2) |-> OUT
    );

    // A1_N low and B2 high force OUT low.
    check_a1_low_b2_high_forces_low: assert property (
        @(posedge clk) (~A1_N & B2) |-> ~OUT
    );

    // A2_N low and B1 high force OUT low.
    check_a2_low_b1_high_forces_low: assert property (
        @(posedge clk) (~A2_N & B1) |-> ~OUT
    );

    // OUT low implies the A1_N/A2_N low term is active.
    check_low_out_implies_a_term_active: assert property (
        @(posedge clk) ~OUT |-> (~A1_N & ~A2_N)
    );

    // OUT low implies the B1/B2 high term is active.
    check_low_out_implies_b_term_active: assert property (
        @(posedge clk) ~OUT |-> (B1 & B2)
    );

    // OUT high implies the A1_N/A2_N low term is inactive.
    check_high_out_implies_a_term_inactive: assert property (
        @(posedge clk) OUT |-> (~(~A1_N & ~A2_N))
    );

    // OUT high implies the B1/B2 high term is inactive.
    check_high_out_implies_b_term_inactive: assert property (
        @(posedge clk) OUT |-> (~(B1 & B2))
    );

endmodule