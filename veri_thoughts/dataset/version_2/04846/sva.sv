module sync_dff_en_W32_sva (
    input logic        clk,
    input logic        en,
    input logic        te,
    input logic [31:0] d,
    input logic [31:0] q
);

    // When enabled in test mode, q captures d by the next clock.
    check_capture_te_branch: assert property (
        @(posedge clk) (en && te) |=> (q == $past(d))
    );

    // When enabled in normal mode, q captures d by the next clock.
    check_capture_normal_branch: assert property (
        @(posedge clk) (en && !te) |=> (q == $past(d))
    );

    // When disabled with te high, q holds its value.
    check_hold_disabled_te_high: assert property (
        @(posedge clk) (!en && te) |=> (q == $past(q))
    );

    // When disabled with te low, q holds its value.
    check_hold_disabled_te_low: assert property (
        @(posedge clk) (!en && !te) |=> (q == $past(q))
    );

    // If enabled and d differs from q, q updates to the new value on the next clock.
    check_update_when_enabled_and_data_differs: assert property (
        @(posedge clk) (en && (d != q)) |=> ((q == $past(d)) && (q != $past(q)))
    );

endmodule