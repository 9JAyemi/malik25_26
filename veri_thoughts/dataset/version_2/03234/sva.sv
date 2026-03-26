module toggle_output_sva (
    input logic        clk,
    input logic        out,
    input logic [31:0] count,
    input logic        clk_divider
);

    // The divider flips on every rising edge of clk.
    check_clk_divider_toggles: assert property (
        @(posedge clk) 1'b1 |=> (clk_divider == ~$past(clk_divider))
    );

    // The counter stays within its programmed terminal range.
    check_count_range: assert property (
        @(posedge clk) (count <= 32'd50000000)
    );

    // When the divider is high, the next clk edge must not update the counter.
    check_count_stable_on_divider_fall: assert property (
        @(posedge clk) (clk_divider == 1'b1) |=> (count == $past(count))
    );

    // When the divider is high, the next clk edge must not update the output.
    check_out_stable_on_divider_fall: assert property (
        @(posedge clk) (clk_divider == 1'b1) |=> (out === $past(out))
    );

    // On an active divider edge below terminal count, the counter increments.
    check_count_increments_on_divider_rise: assert property (
        @(posedge clk) ((clk_divider == 1'b0) && (count != 32'd50000000)) |=> (count == ($past(count) + 32'd1))
    );

    // On an active divider edge at terminal count, the counter wraps to zero.
    check_count_wraps_on_terminal: assert property (
        @(posedge clk) ((clk_divider == 1'b0) && (count == 32'd50000000)) |=> (count == 32'd0)
    );

    // Below terminal count, the output holds through an active divider edge.
    check_out_holds_below_terminal: assert property (
        @(posedge clk) ((clk_divider == 1'b0) && (count != 32'd50000000)) |=> (out === $past(out))
    );

    // At terminal count, the output inverts through an active divider edge.
    check_out_toggles_on_terminal: assert property (
        @(posedge clk) ((clk_divider == 1'b0) && (count == 32'd50000000)) |=> (out === ~$past(out))
    );

    // Any counter change must come from a divider rise on the prior clk.
    check_count_changes_only_on_divider_rise: assert property (
        @(posedge clk) 1'b1 |=> ((count != $past(count)) |-> ($past(clk_divider) == 1'b0))
    );

    // Any output change must come from terminal count on a divider rise.
    check_out_changes_only_on_terminal: assert property (
        @(posedge clk) 1'b1 |=> ((out !== $past(out)) |-> (($past(clk_divider) == 1'b0) && ($past(count) == 32'd50000000)))
    );

endmodule

bind toggle_output toggle_output_sva toggle_output_sva_inst (
    .clk(clk),
    .out(out),
    .count(count),
    .clk_divider(clk_divider)
);