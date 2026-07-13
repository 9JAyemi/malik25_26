module binary_counter_sva (
    input logic clk,
    input logic rst,
    input logic en,
    input logic [3:0] count,
    input logic max
);
    // Clock: clk posedge. Reset: rst active-high, async assert/sync release.
    // Logic: count is sequential; max is combinational decode of count==15.

    // While reset is asserted at the clock edge, count must be 0.
    check_count_zero_when_rst: assert property (
        @(posedge clk) rst |-> (count == 4'h0)
    );

    // While reset is asserted at the clock edge, max must be 0.
    check_max_zero_when_rst: assert property (
        @(posedge clk) rst |-> (max == 1'b0)
    );

    // max reflects count==15 combinationally.
    check_max_decodes_count: assert property (
        @(posedge clk) disable iff (rst) max == (count == 4'hF)
    );

    // If count is 15 and en is 1 at a clock edge, next count wraps to 0.
    check_wrap_on_max_when_en: assert property (
        @(posedge clk) disable iff (rst) (en && (count == 4'hF)) |=> (count == 4'h0)
    );

    // If count is 15 and en is 1 at a clock edge, next max is 0.
    check_max_clears_after_wrap: assert property (
        @(posedge clk) disable iff (rst) (en && (count == 4'hF)) |=> (max == 1'b0)
    );

    // Any change on max corresponds to count==15 condition toggling.
    check_max_change_matches_count15_toggle: assert property (
        @(posedge clk) disable iff (rst) $changed(max) |-> ((count == 4'hF) ^ ($past(count) == 4'hF))
    );

endmodule