module freq_divider_sva (
    input logic clk_in,
    input logic clk_out
);

// clk_in is the only clock; there is no reset in the RTL.
    // The logic is sequential: clk_out toggles every n clock edges.

    // clk_out toggles every n clock edges.
    check_toggle_every_n: assert property (
        @(posedge clk_in) 1'b1 |=> (clk_out == ~$past(clk_out))
    );

// After n clock edges, clk_out returns to its previous value.
    check_period_n: assert property (
        @(posedge clk_in) 1'b1 |-> ##n (clk_out == $past(clk_out, n))
    );

// clk_out is high after n clock edges if it was high before.
    check_high_after_n_high: assert property (
        @(posedge clk_in) 1'b1 |-> ##n (clk_out == $past(clk_out, n) && $past(clk_out))
    );

// clk_out is low after n clock edges if it was low before.
    check_low_after_n_low: assert property (
        @(posedge clk_in) 1'b1 |-> ##n (clk_out == $past(clk_out, n) && !$past(clk_out))
    );

endmodule
