module nor2_sva(
    input logic clk,
    input logic a,
    input logic b,
    input logic out
);

    // No RTL clock/reset; clk samples the combinational NOR output.
    // Output matches the implemented two-input NOR function.
    check_nor2_function: assert property (
        @(posedge clk) out == ~(a | b)
    );

    // A high input forces the output low.
    check_nor2_a_high_forces_low: assert property (
        @(posedge clk) a |-> !out
    );

    // B high input forces the output low.
    check_nor2_b_high_forces_low: assert property (
        @(posedge clk) b |-> !out
    );

    // Both inputs low produce a high output.
    check_nor2_both_low_gives_high: assert property (
        @(posedge clk) (!a && !b) |-> out
    );

    // A high output requires both inputs low.
    check_nor2_high_output_requires_low_inputs: assert property (
        @(posedge clk) out |-> (!a && !b)
    );

endmodule

module nor3_sva(
    input logic clk,
    input logic a,
    input logic b,
    input logic c,
    input logic out
);

    // No RTL clock/reset; clk samples the combinational output.
    // Output matches the implemented logic ((a | b) & ~c).
    check_nor3_function: assert property (
        @(posedge clk) out == ((a | b) & ~c)
    );

    // C high forces the output low.
    check_nor3_c_high_forces_low: assert property (
        @(posedge clk) c |-> !out
    );

    // With A and B both low, the output is low.
    check_nor3_ab_low_forces_low: assert property (
        @(posedge clk) (!a && !b) |-> !out
    );

    // A high with C low makes the output high.
    check_nor3_a_high_c_low_gives_high: assert property (
        @(posedge clk) (a && !c) |-> out
    );

    // B high with C low makes the output high.
    check_nor3_b_high_c_low_gives_high: assert property (
        @(posedge clk) (b && !c) |-> out
    );

    // A high output requires C low.
    check_nor3_high_output_requires_c_low: assert property (
        @(posedge clk) out |-> !c
    );

    // A high output requires at least one of A or B high.
    check_nor3_high_output_requires_ab_high: assert property (
        @(posedge clk) out |-> (a || b)
    );

    // With C low and output low, both A and B must be low.
    check_nor3_c_low_low_output_requires_ab_low: assert property (
        @(posedge clk) (!c && !out) |-> (!a && !b)
    );

endmodule