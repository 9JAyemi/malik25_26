module program_counter_sva (
    input logic [0:31] next_pc,
    input logic [0:31] cur_pc,
    input logic rst,
    input logic clk
);
    // If reset was asserted in the previous cycle, next_pc is zero now.
    prev_reset_forces_zero: assert property (
        @(posedge clk) disable iff (rst) $past(rst) |-> (next_pc == 32'd0)
    );

    // If previous cycle was not reset, next_pc equals previous cur_pc + 4.
    update_plus4_when_not_reset: assert property (
        @(posedge clk) disable iff (rst) !$past(rst) |-> (next_pc == $past(cur_pc) + 32'd4)
    );

    // On the cycle reset deasserts, next_pc is zero (due to prior-cycle reset).
    zero_on_reset_deassertion: assert property (
        @(posedge clk) disable iff (rst) $fell(rst) |-> (next_pc == 32'd0)
    );

    // LSB bit [31] is preserved across +4 updates (when not in reset previously).
    preserve_lsb_bit31: assert property (
        @(posedge clk) disable iff (rst) !$past(rst) |-> (next_pc[31] == $past(cur_pc[31]))
    );

    // LSB bit [30] is preserved across +4 updates (when not in reset previously).
    preserve_lsb_bit30: assert property (
        @(posedge clk) disable iff (rst) !$past(rst) |-> (next_pc[30] == $past(cur_pc[30]))
    );

    // Wrap-around: FFFF_FFFC + 4 -> 0000_0000 when not in reset previously.
    wrap_fffc_to_0000: assert property (
        @(posedge clk) disable iff (rst) (!$past(rst) && ($past(cur_pc) == 32'hFFFF_FFFC)) |-> (next_pc == 32'h0000_0000)
    );

    // Wrap-around: FFFF_FFFF + 4 -> 0000_0003 when not in reset previously.
    wrap_ffff_to_0003: assert property (
        @(posedge clk) disable iff (rst) (!$past(rst) && ($past(cur_pc) == 32'hFFFF_FFFF)) |-> (next_pc == 32'h0000_0003)
    );
endmodule