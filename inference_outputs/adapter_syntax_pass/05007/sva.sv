module nor_gate_using_nand_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic out
);

    // out matches the implemented NAND-of-NANDs function.
    check_out_matches_implemented_function: assert property (
        @(posedge clk) out == ~((~a) & (~b))
    );

    // out is high when both inputs are high.
    check_out_high_when_both_inputs_high: assert property (
        @(posedge clk) (a && b) |-> out
    );

    // out is low when both inputs are low.
    check_out_low_when_both_inputs_low: assert property (
        @(posedge clk) (!a && !b) |-> !out
    );

    // out is low when a is low.
    check_out_low_when_a_low: assert property (
        @(posedge clk) !a |-> !out
    );

    // out is low when b is low.
    check_out_low_when_b_low: assert property (
        @(posedge clk) !b |-> !out
    );

    // out is high when a is high.
    check_out_high_when_a_high: assert property (
        @(posedge clk) a |-> out
    );

    // out is high when b is high.
    check_out_high_when_b_high: assert property (
        @(posedge clk) b |-> out
    );

endmodule