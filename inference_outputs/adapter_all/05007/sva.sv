module nor_gate_using_nand_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic out
);

    // Output matches the implemented NAND-of-NANDs function.
    check_output_function: assert property (
        @(posedge clk) out == ~(~a & ~b)
    );

    // Both inputs high drive the output high.
    check_both_inputs_high_drive_output_high: assert property (
        @(posedge clk) (a && b) |-> out
    );

    // Both inputs low drive the output low.
    check_both_inputs_low_drive_output_low: assert property (
        @(posedge clk) (!a && !b) |-> !out
    );

    // A high and B low drive the output low.
    check_a_high_b_low_drive_output_low: assert property (
        @(posedge clk) (a && !b) |-> !out
    );

    // A low and B high drive the output low.
    check_a_low_b_high_drive_output_low: assert property (
        @(posedge clk) (!a && b) |-> !out
    );

    // A high output requires both inputs high.
    check_output_high_requires_both_inputs_high: assert property (
        @(posedge clk) out |-> (a && b)
    );

    // A low output requires at least one input low.
    check_output_low_requires_some_input_low: assert property (
        @(posedge clk) !out |-> (!a || !b)
    );

endmodule