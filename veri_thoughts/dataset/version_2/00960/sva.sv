module sync_merge_sva (
    input logic clk,
    input logic r1,
    input logic r2,
    input logic a1,
    input logic a2,
    input logic r0,
    input logic a0
);
    // r0 is XOR of r1 and r2.
    check_r0_xor: assert property (
        @(posedge clk) r0 == (r1 ^ r2)
    );

    // When both r1 and r2 are LOW, outputs are LOW.
    check_both_low_behavior: assert property (
        @(posedge clk) (r1 == 1'b0 && r2 == 1'b0) |-> (r0 == 1'b0 && a0 == 1'b0)
    );

    // When only r1 is HIGH, r0 is HIGH and a0 passes a1.
    check_r1_only_behavior: assert property (
        @(posedge clk) (r1 == 1'b1 && r2 == 1'b0) |-> (r0 == 1'b1 && a0 == a1)
    );

    // When only r2 is HIGH, r0 is HIGH and a0 passes a2.
    check_r2_only_behavior: assert property (
        @(posedge clk) (r1 == 1'b0 && r2 == 1'b1) |-> (r0 == 1'b1 && a0 == a2)
    );

    // When both r1 and r2 are HIGH, outputs are LOW.
    check_both_high_behavior: assert property (
        @(posedge clk) (r1 == 1'b1 && r2 == 1'b1) |-> (r0 == 1'b0 && a0 == 1'b0)
    );

    // If r0 is LOW, a0 must be LOW.
    check_r0_low_implies_a0_low: assert property (
        @(posedge clk) (r0 == 1'b0) |-> (a0 == 1'b0)
    );

    // a0 can be HIGH only when exactly one request is HIGH.
    check_a0_high_only_if_one_req: assert property (
        @(posedge clk) (a0 == 1'b1) |-> (r1 ^ r2)
    );

    // On r1 rising when r2 is LOW, r0 is HIGH and a0 passes a1.
    check_rise_r1_when_r2_low: assert property (
        @(posedge clk) ($rose(r1) && (r2 == 1'b0)) |-> (r0 == 1'b1 && a0 == a1)
    );

    // On r2 rising when r1 is LOW, r0 is HIGH and a0 passes a2.
    check_rise_r2_when_r1_low: assert property (
        @(posedge clk) ($rose(r2) && (r1 == 1'b0)) |-> (r0 == 1'b1 && a0 == a2)
    );

    // On r1 falling when r2 is HIGH, r0 is HIGH and a0 passes a2.
    check_fall_r1_when_r2_high: assert property (
        @(posedge clk) ($fell(r1) && (r2 == 1'b1)) |-> (r0 == 1'b1 && a0 == a2)
    );
endmodule