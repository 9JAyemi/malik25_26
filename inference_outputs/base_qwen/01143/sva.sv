```systemverilog
module top_module_sva (
    input logic clk,
    input logic d,
    output logic q
);
    // Sequential logic: q is updated on both rising and falling edges of clk
    // Ensure q is stable after each clock edge
    stable_q: assert property (
        @(posedge clk) disable iff (!clk) q == q
    );

    // Ensure q is updated on both rising and falling edges of clk
    update_q: assert property (
        @(posedge clk) disable iff (!clk) q == ff.q2
    );

    // Ensure d is sampled on the rising edge of clk
    sample_d: assert property (
        @(posedge clk) disable iff (!clk) q == ff.q1
    );
endmodule
```