module top_module_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic out
);

    // Output matches the NOR of the two inputs.
    check_out_is_nor: assert property (
        @(posedge clk) out == ~(a | b)
    );

    // Both low inputs produce a high output.
    check_out_high_when_inputs_low: assert property (
        @(posedge clk) (!a && !b) |-> out
    );

    // A high on a forces the output low.
    check_out_low_when_a_high: assert property (
        @(posedge clk) a |-> !out
    );

    // A high on b forces the output low.
    check_out_low_when_b_high: assert property (
        @(posedge clk) b |-> !out
    );

    // A high output implies both inputs are low.
    check_out_high_implies_inputs_low: assert property (
        @(posedge clk) out |-> (!a && !b)
    );

endmodule