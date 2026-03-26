module freq_div_sva (
    input logic       clk_in,
    input logic       reset,
    input logic [7:0] divider,
    input logic       clk_out
);

    // A sampled reset forces clk_out low on the following clock.
    check_reset_drives_clk_out_low: assert property (
        @(posedge clk_in)
        !$initstate && $past(reset) |-> (clk_out == 1'b0)
    );

    // After reset leaves count at zero, divider=0 causes a toggle on the next active edge.
    check_reset_release_div_zero_toggles: assert property (
        @(posedge clk_in) disable iff (reset)
        !$initstate && $past(reset) && (divider == 8'h00) |=> (clk_out != $past(clk_out))
    );

    // After reset leaves count at zero, divider!=0 prevents a toggle on the next active edge.
    check_reset_release_div_nonzero_holds: assert property (
        @(posedge clk_in) disable iff (reset)
        !$initstate && $past(reset) && (divider != 8'h00) |=> (clk_out == $past(clk_out))
    );

    // Any observed clk_out change leaves count at zero; divider=0 causes another toggle next edge.
    check_change_followed_by_div_zero_toggles: assert property (
        @(posedge clk_in) disable iff (reset)
        !$initstate && (clk_out != $past(clk_out)) && (divider == 8'h00) |=> (clk_out != $past(clk_out))
    );

    // Any observed clk_out change leaves count at zero; divider!=0 holds clk_out on the next edge.
    check_change_followed_by_div_nonzero_holds: assert property (
        @(posedge clk_in) disable iff (reset)
        !$initstate && (clk_out != $past(clk_out)) && (divider != 8'h00) |=> (clk_out == $past(clk_out))
    );

endmodule