module jk_flip_flop_sva (
    input logic J,
    input logic K,
    input logic clk,
    input logic Q
);

    // J=0 and K=0 must hold Q low.
    check_hold_low: assert property (
        @(posedge clk)
        (J === 1'b0 && K === 1'b0 && Q === 1'b0) |=> (Q === 1'b0)
    );

    // J=0 and K=0 must hold Q high.
    check_hold_high: assert property (
        @(posedge clk)
        (J === 1'b0 && K === 1'b0 && Q === 1'b1) |=> (Q === 1'b1)
    );

    // J=0 and K=1 must drive Q low.
    check_reset_output_low: assert property (
        @(posedge clk)
        (J === 1'b0 && K === 1'b1) |=> (Q === 1'b0)
    );

    // J=1 and K=0 must drive Q high.
    check_set_output_high: assert property (
        @(posedge clk)
        (J === 1'b1 && K === 1'b0) |=> (Q === 1'b1)
    );

    // J=1 and K=1 must toggle Q from low to high.
    check_toggle_low_to_high: assert property (
        @(posedge clk)
        (J === 1'b1 && K === 1'b1 && Q === 1'b0) |=> (Q === 1'b1)
    );

    // J=1 and K=1 must toggle Q from high to low.
    check_toggle_high_to_low: assert property (
        @(posedge clk)
        (J === 1'b1 && K === 1'b1 && Q === 1'b1) |=> (Q === 1'b0)
    );

endmodule