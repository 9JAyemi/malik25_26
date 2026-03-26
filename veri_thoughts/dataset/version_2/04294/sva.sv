module counter_sva (
    input logic       clk,
    input logic       rst,
    input logic [3:0] out
);

    // After a reset cycle, the counter is observed at zero.
    check_reset_release_clears_out: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        $past(rst) |-> (out == 4'h0)
    );

    // On consecutive non-reset cycles, values below 15 increment by one.
    check_counter_increments_below_max: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        !$past(rst) && ($past(out) != 4'hF) |-> (out == ($past(out) + 4'h1))
    );

    // On consecutive non-reset cycles, 15 wraps back to zero.
    check_counter_wraps_from_max: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        !$past(rst) && ($past(out) == 4'hF) |-> (out == 4'h0)
    );

    // One cycle after reset release, the counter advances to one.
    check_first_increment_after_reset: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        $past(rst) |=> (out == 4'h1)
    );

endmodule