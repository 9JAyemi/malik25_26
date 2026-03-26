module uart_sync_flops_sva #(
    parameter int width = 1,
    parameter bit init_value = 1'b0
) (
    input logic                 rst_i,
    input logic                 clk_i,
    input logic                 stage1_rst_i,
    input logic                 stage1_clk_en_i,
    input logic [width-1:0]     async_dat_i,
    input logic [width-1:0]     sync_dat_o,
    input logic [width-1:0]     flop_0
);

    // clk_i is the only clock; rst_i is an active-high asynchronous reset.
    // flop_0 is the internal first-stage synchronizer register.

    // After reset was active, the first stage is still at the init value.
    check_stage0_init_after_reset: assert property (
        @(posedge clk_i) disable iff (rst_i)
        $past(rst_i) |-> (flop_0 == {width{init_value}})
    );

    // After reset was active, the second stage is still at the init value.
    check_stage1_init_after_reset: assert property (
        @(posedge clk_i) disable iff (rst_i)
        $past(rst_i) |-> (sync_dat_o == {width{init_value}})
    );

    // The first stage samples async_dat_i on every non-reset clock.
    check_stage0_samples_async: assert property (
        @(posedge clk_i) disable iff (rst_i)
        1'b1 |=> (flop_0 == $past(async_dat_i))
    );

    // stage1_rst_i synchronously clears the second stage.
    check_stage1_sync_reset: assert property (
        @(posedge clk_i) disable iff (rst_i)
        stage1_rst_i |=> (sync_dat_o == {width{init_value}})
    );

    // With stage1 reset inactive and clock enable low, the second stage holds.
    check_stage1_hold_when_disabled: assert property (
        @(posedge clk_i) disable iff (rst_i)
        (!stage1_rst_i && !stage1_clk_en_i) |=> (sync_dat_o == $past(sync_dat_o))
    );

    // With stage1 reset inactive and clock enable high, the second stage captures flop_0.
    check_stage1_captures_stage0: assert property (
        @(posedge clk_i) disable iff (rst_i)
        (!stage1_rst_i && stage1_clk_en_i) |=> (sync_dat_o == $past(flop_0))
    );

    // stage1_rst_i has priority over stage1_clk_en_i in the second stage.
    check_stage1_reset_priority_over_enable: assert property (
        @(posedge clk_i) disable iff (rst_i)
        (stage1_rst_i && stage1_clk_en_i) |=> (sync_dat_o == {width{init_value}})
    );

endmodule