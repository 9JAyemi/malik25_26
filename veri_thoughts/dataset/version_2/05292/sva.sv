module and_gate_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1_N,
    input logic B2_N
);

    // Y must implement the RTL NAND function of the four inputs.
    check_function_equivalence: assert property (
        @(posedge clk) Y === ~(A1 & A2 & B1_N & B2_N)
    );

    // If all four inputs are high, Y must be low.
    check_all_high_drives_low: assert property (
        @(posedge clk)
        (A1 === 1'b1 && A2 === 1'b1 && B1_N === 1'b1 && B2_N === 1'b1) |-> (Y === 1'b0)
    );

    // If A1 is low, Y must be high.
    check_a1_low_drives_high: assert property (
        @(posedge clk)
        (A1 === 1'b0) |-> (Y === 1'b1)
    );

    // If A2 is low, Y must be high.
    check_a2_low_drives_high: assert property (
        @(posedge clk)
        (A2 === 1'b0) |-> (Y === 1'b1)
    );

    // If B1_N is low, Y must be high.
    check_b1_n_low_drives_high: assert property (
        @(posedge clk)
        (B1_N === 1'b0) |-> (Y === 1'b1)
    );

    // If B2_N is low, Y must be high.
    check_b2_n_low_drives_high: assert property (
        @(posedge clk)
        (B2_N === 1'b0) |-> (Y === 1'b1)
    );

    // A low Y can only occur when all four inputs are high.
    check_low_output_requires_all_high: assert property (
        @(posedge clk)
        (Y === 1'b0) |-> (A1 === 1'b1 && A2 === 1'b1 && B1_N === 1'b1 && B2_N === 1'b1)
    );

endmodule