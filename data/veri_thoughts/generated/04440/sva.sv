module ctu_nor2_sva (
    input logic clk,
    input logic z,
    input logic a,
    input logic b
);

    // Output must equal the NOR of the inputs.
    check_nor_function: assert property (
        @(posedge clk) z === ~(a | b)
    );

    // z must be HIGH when both inputs are LOW.
    check_z_high_when_both_low: assert property (
        @(posedge clk) ((a === 1'b0) && (b === 1'b0)) |-> (z === 1'b1)
    );

    // z must be LOW whenever a is HIGH.
    check_z_low_when_a_high: assert property (
        @(posedge clk) (a === 1'b1) |-> (z === 1'b0)
    );

    // z must be LOW whenever b is HIGH.
    check_z_low_when_b_high: assert property (
        @(posedge clk) (b === 1'b1) |-> (z === 1'b0)
    );

    // A HIGH output implies both inputs are LOW.
    check_z_high_implies_both_low: assert property (
        @(posedge clk) (z === 1'b1) |-> ((a === 1'b0) && (b === 1'b0))
    );

endmodule