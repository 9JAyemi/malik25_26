module clk_buffer_driver_sva #(
    parameter int n = 4
) (
    input logic         clk,
    input logic [n-1:0] clk_out
);

    // No reset exists in this RTL.

    // All distributed clock outputs must always be identical.
    check_clk_out_replicated: assert property (
        @(posedge clk) clk_out === {n{clk_out[0]}}
    );

    // Any observed clock edge drives all outputs HIGH by the next cycle.
    check_clk_out_goes_high_next_cycle: assert property (
        @(posedge clk) 1'b1 |=> (clk_out === {n{1'b1}})
    );

    // Once the outputs are HIGH, they remain HIGH on later cycles.
    check_clk_out_stays_high: assert property (
        @(posedge clk) (clk_out === {n{1'b1}}) |=> (clk_out === {n{1'b1}})
    );

endmodule