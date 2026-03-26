module oh_edgealign_sva (
    input logic fastclk,
    input logic slowclk,
    input logic firstedge,
    input logic clk45,
    input logic clk90
);

    // clk45 captures slowclk on each fastclk falling edge.
    check_clk45_captures_slowclk: assert property (
        @(negedge fastclk) 1'b1 |=> (clk45 == $past(slowclk))
    );

    // clk90 captures clk45 on each fastclk rising edge.
    check_clk90_captures_clk45: assert property (
        @(posedge fastclk) 1'b1 |=> (clk90 == $past(clk45))
    );

    // firstedge captures the ~clk45 & clk90 detect term on each fastclk rising edge.
    check_firstedge_captures_detect_term: assert property (
        @(posedge fastclk) 1'b1 |=> (firstedge == ((!$past(clk45)) && $past(clk90)))
    );

    // A sampled clk45=0 and clk90=1 condition must assert firstedge.
    check_firstedge_assert_condition: assert property (
        @(posedge fastclk) ((!clk45) && clk90) |=> (firstedge == 1'b1)
    );

    // All other sampled clk45/clk90 combinations must clear firstedge.
    check_firstedge_clear_condition: assert property (
        @(posedge fastclk) (clk45 || (!clk90)) |=> (firstedge == 1'b0)
    );

endmodule