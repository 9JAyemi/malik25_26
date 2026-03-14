module shift_adder_sva (
    input logic clk,
    input logic load,
    input logic [31:0] a,
    input logic [31:0] b,
    input logic sub,
    input logic [31:0] sum
);

    // Sum equals b when adding, or (0 - b) when subtracting.
    check_sum_function: assert property (
        @(posedge clk) sum == (sub ? (32'h0000_0000 - b) : b)
    );

    // When not subtracting, sum mirrors b.
    check_sum_when_add: assert property (
        @(posedge clk) (!sub) |-> (sum == b)
    );

    // When subtracting, sum + b == 0 (two's complement negation).
    check_sum_when_sub: assert property (
        @(posedge clk) sub |-> ((sum + b) == 32'h0000_0000)
    );

    // If b and sub are stable, sum must remain stable.
    check_sum_stable_if_b_sub_stable: assert property (
        @(posedge clk) $stable(b) && $stable(sub) |-> $stable(sum)
    );

    // If sum changes, either b or sub must have changed.
    check_sum_change_implies_b_or_sub_change: assert property (
        @(posedge clk) $changed(sum) |-> ($changed(b) || $changed(sub))
    );

    // If b is zero, sum must be zero regardless of sub.
    check_sum_zero_when_b_zero: assert property (
        @(posedge clk) (b == 32'h0000_0000) |-> (sum == 32'h0000_0000)
    );

    // Subtracting the most-negative value returns itself (overflow wraps).
    check_sum_minint_case_when_sub: assert property (
        @(posedge clk) (sub && (b == 32'h8000_0000)) |-> (sum == 32'h8000_0000)
    );

    // Changes on a alone (with b and sub stable) cannot change sum.
    check_sum_ignores_a: assert property (
        @(posedge clk) $changed(a) && $stable(b) && $stable(sub) |-> $stable(sum)
    );

    // Changes on load alone (with b and sub stable) cannot change sum.
    check_sum_ignores_load: assert property (
        @(posedge clk) $changed(load) && $stable(b) && $stable(sub) |-> $stable(sum)
    );

    // On sub rising edge with b stable, sum equals (0 - b) in that cycle.
    check_sum_on_sub_rise: assert property (
        @(posedge clk) $rose(sub) && $stable(b) |-> (sum == (32'h0000_0000 - b))
    );

    // On sub falling edge with b stable, sum equals b in that cycle.
    check_sum_on_sub_fall: assert property (
        @(posedge clk) $fell(sub) && $stable(b) |-> (sum == b)
    );

endmodule