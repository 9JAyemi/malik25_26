module clk_div_assertions (
    input logic        clk,
    input logic        rst,
    input logic        SW2,
    input logic [31:0] clkdiv,
    input logic        Clk_CPU
);

    // Clk_CPU is wired directly to clk.
    check_clk_cpu_mirrors_clk: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        (Clk_CPU == clk)
    );

    // A sampled reset must leave clkdiv at zero on the next sampled clock.
    check_clkdiv_zero_after_sampled_reset: assert property (
        @(posedge clk) disable iff ($initstate)
        $past(rst) |-> (clkdiv == 32'd0)
    );

    // Any nonzero sampled count must be the prior sampled count plus one.
    check_clkdiv_increments_for_nonzero_values: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        (clkdiv != 32'd0) |-> (clkdiv == ($past(clkdiv) + 32'd1))
    );

    // A sampled maximum count must wrap back to zero.
    check_clkdiv_wraps_after_max: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        ($past(clkdiv) == 32'hFFFF_FFFF) |-> (clkdiv == 32'd0)
    );

endmodule