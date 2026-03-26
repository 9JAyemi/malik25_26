module omsp_and_gate_sva (
    input logic clk,
    input logic y,
    input logic a,
    input logic b
);

    // Output must equal the AND of the inputs.
    check_y_matches_and_function: assert property (
        @(posedge clk) y == (a & b)
    );

    // A HIGH output requires input a to be HIGH.
    check_y_high_implies_a_high: assert property (
        @(posedge clk) y |-> a
    );

    // A HIGH output requires input b to be HIGH.
    check_y_high_implies_b_high: assert property (
        @(posedge clk) y |-> b
    );

    // Both inputs HIGH must drive the output HIGH.
    check_both_inputs_high_implies_y_high: assert property (
        @(posedge clk) (a & b) |-> y
    );

endmodule