module my_nand2b_sva (
    input logic clk,
    input logic Y,
    input logic A_N,
    input logic B
);

    // Combinational DUT with no reset; sample behavior on clk.

    // Y must match the implemented boolean equation.
    check_boolean_function: assert property (
        @(posedge clk) Y === ((~A_N) & (~B))
    );

    // Both inputs low must drive Y high.
    check_output_high_when_inputs_low: assert property (
        @(posedge clk) ((A_N === 1'b0) && (B === 1'b0)) |-> (Y === 1'b1)
    );

    // A_N high must drive Y low.
    check_output_low_when_a_n_high: assert property (
        @(posedge clk) (A_N === 1'b1) |-> (Y === 1'b0)
    );

    // B high must drive Y low.
    check_output_low_when_b_high: assert property (
        @(posedge clk) (B === 1'b1) |-> (Y === 1'b0)
    );

    // Y high implies both inputs are low.
    check_output_high_only_when_inputs_low: assert property (
        @(posedge clk) (Y === 1'b1) |-> ((A_N === 1'b0) && (B === 1'b0))
    );

endmodule