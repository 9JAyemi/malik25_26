module alt_ddrx_clock_and_reset_sva #
(
    parameter CTL_RESET_SYNC_STAGES      = 4,
    parameter CTL_NUM_RESET_OUTPUT       = 1,
    parameter CTL_HALF_RESET_SYNC_STAGES = 4,
    parameter CTL_HALF_NUM_RESET_OUTPUT  = 1
)
(
    input  logic                                       ctl_clk,
    input  logic                                       ctl_reset_n,
    input  logic                                       ctl_half_clk,
    input  logic                                       ctl_half_clk_reset_n,
    input  logic [CTL_NUM_RESET_OUTPUT-1:0]           resynced_ctl_reset_n,
    input  logic [CTL_HALF_NUM_RESET_OUTPUT-1:0]      resynced_ctl_half_clk_reset_n
);

localparam logic [CTL_NUM_RESET_OUTPUT-1:0]      CTL_RESET_ZERO      = {CTL_NUM_RESET_OUTPUT{1'b0}};
localparam logic [CTL_NUM_RESET_OUTPUT-1:0]      CTL_RESET_ONE       = {CTL_NUM_RESET_OUTPUT{1'b1}};
localparam logic [CTL_HALF_NUM_RESET_OUTPUT-1:0] CTL_HALF_RESET_ZERO = {CTL_HALF_NUM_RESET_OUTPUT{1'b0}};
localparam logic [CTL_HALF_NUM_RESET_OUTPUT-1:0] CTL_HALF_RESET_ONE  = {CTL_HALF_NUM_RESET_OUTPUT{1'b1}};

    // Active-low ctl reset clears the synchronized ctl reset outputs.
    check_ctl_reset_asserts_zero: assert property (
        @(posedge ctl_clk)
        (!ctl_reset_n) |-> (resynced_ctl_reset_n == CTL_RESET_ZERO)
    );

    // After ctl reset release, the synchronized ctl reset stays low for the programmed latency.
    check_ctl_reset_release_latency: assert property (
        @(posedge ctl_clk) disable iff (!ctl_reset_n)
        $rose(ctl_reset_n) |-> (resynced_ctl_reset_n == CTL_RESET_ZERO)[*CTL_RESET_SYNC_STAGES]
    );

    // After ctl reset release, the synchronized ctl reset deasserts on time and stays high on the next cycle.
    check_ctl_reset_release_deasserts_and_holds: assert property (
        @(posedge ctl_clk) disable iff (!ctl_reset_n)
        $rose(ctl_reset_n) |-> ##CTL_RESET_SYNC_STAGES
                              (resynced_ctl_reset_n == CTL_RESET_ONE)
                              ##1
                              (resynced_ctl_reset_n == CTL_RESET_ONE)
    );

    // Active-low half-rate reset clears the synchronized half-rate reset outputs.
    check_half_reset_asserts_zero: assert property (
        @(posedge ctl_half_clk)
        (!ctl_half_clk_reset_n) |-> (resynced_ctl_half_clk_reset_n == CTL_HALF_RESET_ZERO)
    );

    // After half-rate reset release, the synchronized half-rate reset stays low for the programmed latency.
    check_half_reset_release_latency: assert property (
        @(posedge ctl_half_clk) disable iff (!ctl_half_clk_reset_n)
        $rose(ctl_half_clk_reset_n) |-> (resynced_ctl_half_clk_reset_n == CTL_HALF_RESET_ZERO)[*CTL_HALF_RESET_SYNC_STAGES]
    );

    // After half-rate reset release, the synchronized half-rate reset deasserts on time and stays high on the next cycle.
    check_half_reset_release_deasserts_and_holds: assert property (
        @(posedge ctl_half_clk) disable iff (!ctl_half_clk_reset_n)
        $rose(ctl_half_clk_reset_n) |-> ##CTL_HALF_RESET_SYNC_STAGES
                                       (resynced_ctl_half_clk_reset_n == CTL_HALF_RESET_ONE)
                                       ##1
                                       (resynced_ctl_half_clk_reset_n == CTL_HALF_RESET_ONE)
    );

endmodule