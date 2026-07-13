module nor_gate_using_nand_sva (
    input logic a,
    input logic b,
    output logic out
);
    // The logic is purely combinational, so we will use @(posedge clk) for assertions.
    // No clock or reset signals are present in the RTL.

    // The output 'out' should be the NOR of 'a' and 'b'.
    // This means 'out' should be 1 if both 'a' and 'b' are 0, and 0 otherwise.
    nor_behavior: assert property (
        @(posedge clk) $rose(out) |-> (a == 1'b0) && (b == 1'b0)
    );
    nor_behavior_neg: assert property (
        @(posedge clk) $fell(out) |-> (a != 1'b0) || (b != 1'b0)
    );
endmodule