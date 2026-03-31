module nor_gate_using_nand_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic out
);

    // Output implements the NOR of the two inputs.
    check_out_is_nor: assert property (
        @(posedge clk) out == ~(a | b)
    );

    // A high on input a forces the output low.
    check_a_high_forces_low: assert property (
        @(posedge clk) a |-> !out
    );

    // A high on input b forces the output low.
    check_b_high_forces_low: assert property (
        @(posedge clk) b |-> !out
    );

    // Both inputs low force the output high.
    check_both_low_forces_high: assert property (
        @(posedge clk) (!a && !b) |-> out
    );

endmodule