module zynq_reset_sva (
    input logic slowest_sync_clk,
    input logic ext_reset_in,
    input logic aux_reset_in,
    input logic mb_debug_sys_rst,
    input logic dcm_locked,
    input logic mb_reset,
    input logic [0:0] bus_struct_reset,
    input logic [0:0] peripheral_reset,
    input logic [0:0] interconnect_aresetn,
    input logic [0:0] peripheral_aresetn
);

    // mb_reset matches its combinational definition.
    check_mb_reset_definition: assert property (
        @(posedge slowest_sync_clk) disable iff (1'b0)
        mb_reset == (mb_debug_sys_rst || ext_reset_in || !dcm_locked)
    );

    // Debug reset forces mb_reset high.
    check_mb_reset_on_debug_reset: assert property (
        @(posedge slowest_sync_clk) disable iff (1'b0)
        mb_debug_sys_rst |-> mb_reset
    );

    // External reset forces mb_reset high.
    check_mb_reset_on_ext_reset: assert property (
        @(posedge slowest_sync_clk) disable iff (1'b0)
        ext_reset_in |-> mb_reset
    );

    // Loss of dcm lock forces mb_reset high.
    check_mb_reset_on_dcm_unlock: assert property (
        @(posedge slowest_sync_clk) disable iff (1'b0)
        !dcm_locked |-> mb_reset
    );

    // mb_reset is low when all of its causes are inactive.
    check_mb_reset_clear_condition: assert property (
        @(posedge slowest_sync_clk) disable iff (1'b0)
        (!mb_debug_sys_rst && !ext_reset_in && dcm_locked) |-> !mb_reset
    );

    // bus_struct_reset mirrors ext_reset_in.
    check_bus_struct_reset_definition: assert property (
        @(posedge slowest_sync_clk) disable iff (1'b0)
        bus_struct_reset[0] == ext_reset_in
    );

    // peripheral_reset mirrors aux_reset_in.
    check_peripheral_reset_definition: assert property (
        @(posedge slowest_sync_clk) disable iff (1'b0)
        peripheral_reset[0] == aux_reset_in
    );

    // interconnect_aresetn is the inverse of mb_reset.
    check_interconnect_aresetn_definition: assert property (
        @(posedge slowest_sync_clk) disable iff (1'b0)
        interconnect_aresetn[0] == !mb_reset
    );

    // peripheral_aresetn is low when mb_reset or peripheral_reset is high.
    check_peripheral_aresetn_definition: assert property (
        @(posedge slowest_sync_clk) disable iff (1'b0)
        peripheral_aresetn[0] == !(mb_reset || peripheral_reset[0])
    );

endmodule