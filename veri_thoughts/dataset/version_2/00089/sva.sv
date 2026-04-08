module power_ground_module_sva (
    input logic clk,
    input logic rst_n,
    input logic enable,
    input logic VPWR,
    input logic VGND
);

    // Clock: clk; reset: rst_n active-low; logic is sequential.
    // VPWR follows enable on the next clocked state update, and VGND is always low.

    // If reset is low, both outputs are low by the next sampled clock.
    check_reset_clears_outputs: assert property (
        @(posedge clk) !rst_n |=> (VPWR == 1'b0 && VGND == 1'b0)
    );

    // Outside reset, the next sampled outputs match the current enable value.
    check_outputs_follow_enable: assert property (
        @(posedge clk) disable iff (!rst_n)
        1'b1 |=> ((VPWR == $past(enable)) && (VGND == 1'b0))
    );

    // When enable is high, the next registered outputs are VPWR=1 and VGND=0.
    check_enable_sets_outputs: assert property (
        @(posedge clk) disable iff (!rst_n)
        enable |=> (VPWR == 1'b1 && VGND == 1'b0)
    );

    // When enable is low, the next registered outputs are VPWR=0 and VGND=0.
    check_disable_clears_outputs: assert property (
        @(posedge clk) disable iff (!rst_n)
        !enable |=> (VPWR == 1'b0 && VGND == 1'b0)
    );

endmodule