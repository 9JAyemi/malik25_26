module top_module_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic c,
    input logic out
);

    // Output matches the implemented combinational function.
    check_out_matches_function: assert property (
        @(posedge clk) out == ((a | b) & ~c)
    );

    // A high c forces the output low.
    check_c_high_forces_out_low: assert property (
        @(posedge clk) c |-> !out
    );

    // With c low, the output behaves as a OR b.
    check_c_low_reduces_to_a_or_b: assert property (
        @(posedge clk) !c |-> (out == (a | b))
    );

    // With c low and a high, the output is high.
    check_c_low_a_high_sets_out: assert property (
        @(posedge clk) (!c && a) |-> out
    );

    // With c low and b high, the output is high.
    check_c_low_b_high_sets_out: assert property (
        @(posedge clk) (!c && b) |-> out
    );

    // With both a and b low, the output is low.
    check_a_b_low_clear_out: assert property (
        @(posedge clk) (!a && !b) |-> !out
    );

    // A high output requires c to be low.
    check_out_high_requires_c_low: assert property (
        @(posedge clk) out |-> !c
    );

    // A high output requires at least one of a or b to be high.
    check_out_high_requires_a_or_b: assert property (
        @(posedge clk) out |-> (a | b)
    );

endmodule