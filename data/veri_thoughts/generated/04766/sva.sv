module pipeline_reg_sva (
    input logic clk,
    input logic rst,
    input logic data,
    input logic out
);

    // Reset makes the sampled output low on the next clock.
    check_reset_clears_output_next_cycle: assert property (
        @(posedge clk) rst |=> (out == 1'b0)
    );

    // Reset keeps the sampled output low two clocks later.
    check_reset_clears_output_two_cycles_later: assert property (
        @(posedge clk) rst |=> ##1 (out == 1'b0)
    );

    // Reset keeps the sampled output low three clocks later.
    check_reset_clears_output_three_cycles_later: assert property (
        @(posedge clk) rst |=> ##2 (out == 1'b0)
    );

    // Reset keeps the sampled output low four clocks later.
    check_reset_clears_output_four_cycles_later: assert property (
        @(posedge clk) rst |=> ##3 (out == 1'b0)
    );

    // After four reset-free samples, out matches data from four samples earlier.
    check_output_matches_four_cycle_old_data: assert property (
        @(posedge clk) disable iff (rst)
        (!$past(rst,1) && !$past(rst,2) && !$past(rst,3) && !$past(rst,4))
        |-> (out == $past(data,4))
    );

    // A delayed rising data transition causes a rising output transition.
    check_delayed_rise_reaches_output: assert property (
        @(posedge clk) disable iff (rst)
        (!$past(rst,1) && !$past(rst,2) && !$past(rst,3) && !$past(rst,4) && !$past(rst,5) &&
         !$past(data,5) && $past(data,4))
        |-> $rose(out)
    );

    // A delayed falling data transition causes a falling output transition.
    check_delayed_fall_reaches_output: assert property (
        @(posedge clk) disable iff (rst)
        (!$past(rst,1) && !$past(rst,2) && !$past(rst,3) && !$past(rst,4) && !$past(rst,5) &&
         $past(data,5) && !$past(data,4))
        |-> $fell(out)
    );

endmodule