module DivFrec_assertions (
    input logic clk,
    input logic rst,
    input logic [10:0] div,
    input logic clkd,
    input logic clk_1kHz,
    input logic [10:0] q,
    input logic cd,
    input logic [15:0] q_1kHz,
    input logic cd_1kHz
);

    // clkd must mirror the internal divider flop.
    check_clkd_reflects_cd: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        clkd == cd
    );

    // clk_1kHz must mirror the internal 1 kHz divider flop.
    check_clk_1khz_reflects_cd_1khz: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        clk_1kHz == cd_1kHz
    );

    // After a sampled reset cycle, the main divider state must be cleared.
    check_main_reset_release_state: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        $past(rst) |-> (q == 11'd0 && cd == 1'b0 && clkd == 1'b0)
    );

    // After a sampled reset cycle, the 1 kHz divider state must be cleared.
    check_fixed_reset_release_state: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        $past(rst) |-> (q_1kHz == 16'd0 && cd_1kHz == 1'b0 && clk_1kHz == 1'b0)
    );

    // The programmable counter increments when it is not at its terminal count.
    check_main_counter_increments: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        (!$past(rst) && ($past(q) != $past(div))) |-> (q == ($past(q) + 11'd1))
    );

    // The programmable divider output holds when the terminal count is not reached.
    check_main_divider_holds_between_terminals: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        (!$past(rst) && ($past(q) != $past(div))) |-> (cd == $past(cd))
    );

    // The programmable counter clears when it reaches div.
    check_main_counter_resets_at_terminal: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        (!$past(rst) && ($past(q) == $past(div))) |-> (q == 11'd0)
    );

    // The programmable divider output toggles when q reaches div.
    check_main_divider_toggles_at_terminal: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        (!$past(rst) && ($past(q) == $past(div))) |-> (cd != $past(cd))
    );

    // The 1 kHz counter increments when it is not at 49999.
    check_fixed_counter_increments: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        (!$past(rst) && ($past(q_1kHz) != 16'd49999)) |-> (q_1kHz == ($past(q_1kHz) + 16'd1))
    );

    // The 1 kHz divider output holds when 49999 is not reached.
    check_fixed_divider_holds_between_terminals: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        (!$past(rst) && ($past(q_1kHz) != 16'd49999)) |-> (cd_1kHz == $past(cd_1kHz))
    );

    // The 1 kHz counter clears when it reaches 49999.
    check_fixed_counter_resets_at_terminal: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        (!$past(rst) && ($past(q_1kHz) == 16'd49999)) |-> (q_1kHz == 16'd0)
    );

    // The 1 kHz divider output toggles when q_1kHz reaches 49999.
    check_fixed_divider_toggles_at_terminal: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        (!$past(rst) && ($past(q_1kHz) == 16'd49999)) |-> (cd_1kHz != $past(cd_1kHz))
    );

    // The fixed divider counter must stay within its implemented count range.
    check_fixed_counter_range: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        q_1kHz <= 16'd49999
    );

endmodule