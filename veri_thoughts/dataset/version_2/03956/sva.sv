module pipelined_xor_assertions(
    input logic clk,
    input logic a,
    input logic b,
    input logic out_comb
);

    // Clock: clk; the RTL has no reset.
    // out_comb is the registered XOR of a and b with two-cycle latency.

    // A low sampled XOR must produce a low output two clocks later.
    check_xor_zero_produces_low: assert property (
        @(posedge clk)
        ((a ^ b) == 1'b0) |-> ##2 (out_comb == 1'b0)
    );

    // A high sampled XOR must produce a high output two clocks later.
    check_xor_one_produces_high: assert property (
        @(posedge clk)
        ((a ^ b) == 1'b1) |-> ##2 (out_comb == 1'b1)
    );

    // A rising sampled XOR must appear as a rising output two clocks later.
    check_xor_rise_propagates: assert property (
        @(posedge clk)
        $rose(a ^ b) |-> ##2 $rose(out_comb)
    );

    // A falling sampled XOR must appear as a falling output two clocks later.
    check_xor_fall_propagates: assert property (
        @(posedge clk)
        $fell(a ^ b) |-> ##2 $fell(out_comb)
    );

    // A stable sampled XOR must keep the output stable two clocks later.
    check_xor_stable_propagates: assert property (
        @(posedge clk)
        $stable(a ^ b) |-> ##2 $stable(out_comb)
    );

endmodule