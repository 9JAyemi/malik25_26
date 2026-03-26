module clk_generator_sva (
    input logic clk_i,
    input logic clk_core,
    input logic clk_bus
);

    // clk_bus directly mirrors clk_i.
    check_clk_bus_matches_clk_i: assert property (
        @(posedge clk_i) clk_bus === clk_i
    );

    // clk_core is initialized low before the first sampled toggle.
    check_clk_core_starts_low: assert property (
        @(posedge clk_i)
        (($past(clk_core) !== 1'b0) && ($past(clk_core) !== 1'b1)) |-> (clk_core === 1'b0)
    );

    // clk_core is always a known binary value when sampled.
    check_clk_core_known: assert property (
        @(posedge clk_i) (clk_core === 1'b0) || (clk_core === 1'b1)
    );

    // A sampled low clk_core flips high on the next clk_i edge.
    check_clk_core_low_to_high: assert property (
        @(posedge clk_i) (clk_core === 1'b0) |=> (clk_core === 1'b1)
    );

    // A sampled high clk_core flips low on the next clk_i edge.
    check_clk_core_high_to_low: assert property (
        @(posedge clk_i) (clk_core === 1'b1) |=> (clk_core === 1'b0)
    );

endmodule