module counter_4bit_sva (
    input logic clk,
    input logic rst,
    input logic [3:0] q
);
    // Synchronous reset drives q to 0 on the reset cycle.
    check_reset_sets_zero: assert property (
        @(posedge clk) rst |-> (q == 4'b0000)
    );

    // When not in reset in consecutive cycles and prev q != 15, q increments by 1.
    check_increment_when_not_max: assert property (
        @(posedge clk) disable iff (rst)
            ($past(!rst) && ($past(q) != 4'hF)) |-> (q == ($past(q) + 4'h1))
    );

    // When not in reset in consecutive cycles and prev q == 15, q rolls over to 0.
    check_rollover_when_max: assert property (
        @(posedge clk) disable iff (rst)
            ($past(!rst) && ($past(q) == 4'hF)) |-> (q == 4'h0)
    );

    // First non-reset cycle after reset deasserts produces q == 1.
    check_first_cycle_after_reset: assert property (
        @(posedge clk) disable iff (rst)
            ($past(rst) && !rst) |-> (q == 4'h1)
    );

    // Without reset now and previously, q==0 can only follow a previous 15.
    check_zero_only_after_max_without_reset: assert property (
        @(posedge clk) disable iff (rst)
            ($past(!rst) && !rst && (q == 4'h0)) |-> ($past(q) == 4'hF)
    );
endmodule