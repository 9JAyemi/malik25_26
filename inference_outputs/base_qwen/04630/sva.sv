module timer_sva (
    input logic wb_clk_i,
    input logic wb_rst_i,
    input logic wb_tgc_o
);
    // Timer counter increments on each clock edge
    counter_increments: assert property (
        @(posedge wb_clk_i) disable iff (!wb_rst_i) cnt == (cnt + phase)
    );

    // clk2 is the least significant bit of the counter
    clk2_assignment: assert property (
        @(posedge wb_clk_i) disable iff (!wb_rst_i) clk2 == cnt[res-1]
    );

    // wb_tgc_o is asserted when clk2 transitions from 0 to 1
    wb_tgc_o_assertion: assert property (
        @(posedge wb_clk_i) disable iff (!wb_rst_i) $rose(clk2) |-> wb_tgc_o == 1'b1
    );

    // wb_tgc_o is deasserted when clk2 transitions from 1 to 0
    wb_tgc_o_deassertion: assert property (
        @(posedge wb_clk_i) disable iff (!wb_rst_i) $fell(clk2) |-> wb_tgc_o == 1'b0
    );

    // wb_tgc_o is deasserted at reset
    wb_tgc_o_reset: assert property (
        @(posedge wb_clk_i) !wb_rst_i |-> wb_tgc_o == 1'b0
    );

    // wb_tgc_o is deasserted when clk2 is 0
    wb_tgc_o_when_clk2_zero: assert property (
        @(posedge wb_clk_i) disable iff (!wb_rst_i) clk2 == 1'b0 |-> wb_tgc_o == 1'b0
    );

    // wb_tgc_o is asserted when clk2 is 1
    wb_tgc_o_when_clk2_one: assert property (
        @(posedge wb_clk_i) disable iff (!wb_rst_i) clk2 == 1'b1 |-> wb_tgc_o == 1'b1
    );

    // Counter wraps around at its maximum value
    counter_wraparound: assert property (
        @(posedge wb_clk_i) disable iff (!wb_rst_i) cnt == (2**res - 1) |-> cnt == 0
    );

    // clk2 is a delayed version of the counter
    clk2_delayed: assert property (
        @(posedge wb_clk_i) disable iff (!wb_rst_i) old_clk2 == cnt[res-2]
    );

    // wb_tgc_o is deasserted when old_clk2 is 1 and clk2 is 0
    wb_tgc_o_when_old_clk2_one_clk2_zero: assert property (
        @(posedge wb_clk_i) disable iff (!wb_rst_i) old_clk2 == 1'b1 && clk2 == 1'b0 |-> wb_tgc_o == 1'b0
    );
endmodule