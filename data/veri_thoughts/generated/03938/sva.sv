module FrequencyDivider_sva #(
    parameter integer Ts = 80,
    parameter integer Te = 20,
    parameter integer n = ((Ts/(2*Te))-1),
    parameter integer bitCount = 31
) (
    input  logic                clk,
    input  logic                clk_out,
    input  logic                rst,
    input  logic [bitCount:0]   counter
);

    // A sampled reset cycle must release reset and clear the state by the next clock.
    check_reset_releases_and_clears_state: assert property (
        @(posedge clk) (!rst) |=> (rst && (counter == '0) && (clk_out == 1'b0))
    );

    // Once reset is released, it stays deasserted.
    check_rst_stays_high_after_release: assert property (
        @(posedge clk) disable iff (!rst) rst |=> rst
    );

    // In active operation, the counter never exceeds the terminal count.
    check_counter_within_range: assert property (
        @(posedge clk) disable iff (!rst) (counter <= n)
    );

    // Before terminal count, the counter increments by one each cycle.
    check_counter_increments_before_terminal_count: assert property (
        @(posedge clk) disable iff (!rst)
        (counter < n) |=> (counter == ($past(counter) + 1'b1))
    );

    // Before terminal count, clk_out holds its value.
    check_clk_out_holds_before_terminal_count: assert property (
        @(posedge clk) disable iff (!rst)
        (counter < n) |=> (clk_out == $past(clk_out))
    );

    // At terminal count, the counter wraps back to zero.
    check_counter_wraps_at_terminal_count: assert property (
        @(posedge clk) disable iff (!rst)
        (counter == n) |=> (counter == '0)
    );

    // At terminal count, clk_out toggles.
    check_clk_out_toggles_at_terminal_count: assert property (
        @(posedge clk) disable iff (!rst)
        (counter == n) |=> (clk_out != $past(clk_out))
    );

endmodule