module uart_sync_flops_sva #(
    parameter width      = 1,
    parameter init_value = 1'b0
) (
    input  logic                  rst_i,
    input  logic                  clk_i,
    input  logic                  stage1_rst_i,
    input  logic                  stage1_clk_en_i,
    input  logic [width-1:0]      async_dat_i,
    input  logic [width-1:0]      sync_dat_o
);
    localparam logic [width-1:0] INIT = {width{init_value}};

    ///// Reset behavior /////
    // While global reset is asserted, sync_dat_o must be INIT.
    check_sync_init_while_rst: assert property (
        @(posedge clk_i) rst_i |-> (sync_dat_o == INIT)
    );

    ///// Stage1 reset behavior /////
    // stage1_rst_i sets sync_dat_o to INIT on the next cycle.
    check_stage1_reset_sets_init: assert property (
        @(posedge clk_i) disable iff (rst_i) stage1_rst_i |-> ##1 (sync_dat_o == INIT)
    );

    // stage1_rst_i has priority over enable when both are HIGH.
    check_stage1_reset_priority_over_enable: assert property (
        @(posedge clk_i) disable iff (rst_i) (stage1_rst_i && stage1_clk_en_i) |-> ##1 (sync_dat_o == INIT)
    );

    ///// Enable/hold behavior /////
    // With no resets and enable LOW, sync_dat_o holds its value.
    check_hold_when_disabled: assert property (
        @(posedge clk_i) disable iff (rst_i) (!stage1_rst_i && !stage1_clk_en_i) |-> ##1 (sync_dat_o == $past(sync_dat_o))
    );

    // If sync_dat_o changes without global reset, prior enable or stage1 reset must be the cause.
    check_change_requires_enable_or_stage1_reset: assert property (
        @(posedge clk_i) disable iff (rst_i) ($changed(sync_dat_o) && !$past(rst_i)) |-> ($past(stage1_clk_en_i) || $past(stage1_rst_i))
    );

    ///// Dataflow through the two-stage synchronizer /////
    // With no resets now and previously, enable updates sync_dat_o from prior async_dat_i.
    check_enable_updates_from_prev_input: assert property (
        @(posedge clk_i) disable iff (rst_i)
            (stage1_clk_en_i && !stage1_rst_i && !$past(rst_i)) |-> ##1 (sync_dat_o == $past(async_dat_i))
    );

    // If previous cycle was under global reset, enable updates sync_dat_o to INIT.
    check_enable_updates_to_init_after_prev_reset: assert property (
        @(posedge clk_i) disable iff (rst_i)
            (stage1_clk_en_i && !stage1_rst_i && $past(rst_i)) |-> ##1 (sync_dat_o == INIT)
    );
endmodule