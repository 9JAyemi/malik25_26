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
        @(posedge clk) OUT == ((A1_N & B2) | (A2_N & B1))
    );

    // A1_N low forces OUT low.
    check_a1n_low_forces_out_low: assert property (
        @(posedge clk) !A1_N |-> !OUT
    );

    // A2_N low forces OUT low.
    check_a2n_low_forces_out_low: assert property (
        @(posedge clk) !A2_N |-> !OUT
    );

    // B1 low forces OUT low.
    check_b1_low_forces_out_low: assert property (
        @(posedge clk) !B1 |-> !OUT
    );

    // B2 low forces OUT low.
    check_b2_low_forces_out_low: assert property (
        @(posedge clk) !B2 |-> !OUT
    );

    // Both A inputs high force OUT high.
    check_a_inputs_high_force_out_high: assert property (
        @(posedge clk) (A1_N & A2_N) |-> OUT
    );

    // Both B inputs high force OUT high.
    check_b_inputs_high_force_out_high: assert property (
        @(posedge clk) (B1 & B2) |-> OUT
    );

    // OUT high requires at least one A input and one B input high.
    check_out_high_requires_active_inputs: assert property (
        @(posedge clk) OUT |-> (A1_N & A2_N & B1 & B2)
    );

    // With A1_N and B1 high, OUT reduces to A2_N & B2.
    check_a1n_b1_high_reduces_to_a2n_b2: assert property (
        @(posedge clk) (A1_N & B1) |-> (OUT == (A2_N & B2))
    );

    // With A2_N and B2 high, OUT reduces to A1_N & B1.
    check_a2n_b2_high_reduces_to_a1n_b1: assert property (
        @(posedge clk) (A2_N & B2) |-> (OUT == (A1_N & B1))
    );

    // With A1_N and B2 high, OUT reduces to A2_N & B1.
    check_a1n_b2_high_reduces_to_a2n_b1: assert property (
        @(posedge clk) (A1_N & B2) |-> (OUT == (A2_N & B1))
    );

    // With A2_N and B1 high, OUT reduces to A1_N & B2.
    check_a2n_b1_high_reduces_to_a1n_b2: assert property (
        @(posedge clk) (A2_N & B1) |-> (OUT == (A1_N & B2))
    );

endmodule