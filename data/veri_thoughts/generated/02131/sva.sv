module add_sub_sva (
    input logic clk,
    input logic [3:0] a,
    input logic [3:0] b,
    input logic sub,
    input logic [3:0] result
);
    // When sub=0, result is 4-bit sum of a and b.
    check_add_when_sub0: assert property (
        @(posedge clk) (!sub) |-> (result == (a + b)[3:0])
    );

    // When sub=1, result is 4-bit difference a - b.
    check_sub_when_sub1: assert property (
        @(posedge clk) (sub) |-> (result == (a - b)[3:0])
    );

    // Result equals mux of add/sub based on sub control.
    check_mux_equivalence: assert property (
        @(posedge clk) result == (sub ? (a - b)[3:0] : (a + b)[3:0])
    );

    // If inputs are stable across cycles, result remains stable.
    check_result_stable_if_inputs_stable: assert property (
        @(posedge clk) $stable({a,b,sub}) |-> $stable(result)
    );

    // On sub rising edge with a,b stable, result switches from sum to diff.
    check_switch_to_sub_on_rise: assert property (
        @(posedge clk) ($rose(sub) && $stable(a) && $stable(b))
            |-> (result == (a - b)[3:0]) && ($past(result) == (($past(a) + $past(b))[3:0]))
    );

    // On sub falling edge with a,b stable, result switches from diff to sum.
    check_switch_to_add_on_fall: assert property (
        @(posedge clk) ($fell(sub) && $stable(a) && $stable(b))
            |-> (result == (a + b)[3:0]) && ($past(result) == (($past(a) - $past(b))[3:0]))
    );
endmodule