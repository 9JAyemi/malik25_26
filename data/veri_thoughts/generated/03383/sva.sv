module clock_gate_sva (
    input logic clk,
    input logic enable,
    input logic clk_out
);

    // clk_out must go high on the cycle after enable is high.
    check_clk_out_set_on_enable: assert property (
        @(posedge clk) enable |=> (clk_out == 1'b1)
    );

    // clk_out must go low on the cycle after enable is low.
    check_clk_out_clear_on_disable: assert property (
        @(posedge clk) !enable |=> (clk_out == 1'b0)
    );

    // clk_out must always match the previous cycle's enable value.
    check_clk_out_matches_prior_enable: assert property (
        @(posedge clk) 1'b1 |=> (clk_out == $past(enable))
    );

endmodule