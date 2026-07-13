module mutex_sva (
    input logic clk,
    input logic G1,
    input logic G2,
    input logic R1,
    input logic R2
);

    // G1 matches the implemented inversion and AND logic.
    check_g1_function: assert property (
        @(posedge clk) (G1 === ((~R1) & R2))
    );

    // G2 matches the implemented inversion and AND logic.
    check_g2_function: assert property (
        @(posedge clk) (G2 === ((~R2) & R1))
    );

    // The two grants are never asserted at the same time.
    check_grants_mutex: assert property (
        @(posedge clk) !((G1 === 1'b1) && (G2 === 1'b1))
    );

    // When both requests are low, both grants are low.
    check_both_requests_low: assert property (
        @(posedge clk) ((R1 === 1'b0) && (R2 === 1'b0)) |-> ((G1 === 1'b0) && (G2 === 1'b0))
    );

    // When both requests are high, both grants are low.
    check_both_requests_high: assert property (
        @(posedge clk) ((R1 === 1'b1) && (R2 === 1'b1)) |-> ((G1 === 1'b0) && (G2 === 1'b0))
    );

    // R1 low and R2 high produces only G1.
    check_r2_only_grants_g1: assert property (
        @(posedge clk) ((R1 === 1'b0) && (R2 === 1'b1)) |-> ((G1 === 1'b1) && (G2 === 1'b0))
    );

    // R1 high and R2 low produces only G2.
    check_r1_only_grants_g2: assert property (
        @(posedge clk) ((R1 === 1'b1) && (R2 === 1'b0)) |-> ((G1 === 1'b0) && (G2 === 1'b1))
    );

    // A high G1 can only occur for the implemented input combination.
    check_g1_implies_inputs: assert property (
        @(posedge clk) (G1 === 1'b1) |-> ((R1 === 1'b0) && (R2 === 1'b1))
    );

    // A high G2 can only occur for the implemented input combination.
    check_g2_implies_inputs: assert property (
        @(posedge clk) (G2 === 1'b1) |-> ((R1 === 1'b1) && (R2 === 1'b0))
    );

endmodule