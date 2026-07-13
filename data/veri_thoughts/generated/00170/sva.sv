module counter_sva (
    input logic clk,
    input logic rst,
    input logic enable,
    input logic count_dir,
    input logic dual_count,
    input logic [7:0] count_out
);

    // Reset forces the counter output to zero.
    check_reset_clears_count: assert property (
        @(posedge clk) !rst |-> (count_out == 8'h00)
    );

    // The counter holds its value when enable is low.
    check_hold_when_disabled: assert property (
        @(posedge clk) disable iff (!rst)
        (!$initstate && $past(rst) && !$past(enable))
        |-> (count_out == $past(count_out))
    );

    // Counting up from 8'hFF wraps to 8'h00.
    check_up_wrap_from_ff: assert property (
        @(posedge clk) disable iff (!rst)
        (!$initstate && $past(rst) && $past(enable) &&
         ($past(count_dir) == 1'b0) && ($past(count_out) == 8'hFF))
        |-> (count_out == 8'h00)
    );

    // Counting down from 8'h00 wraps to 8'hFF.
    check_down_wrap_from_zero: assert property (
        @(posedge clk) disable iff (!rst)
        (!$initstate && $past(rst) && $past(enable) &&
         ($past(count_dir) == 1'b1) && ($past(count_out) == 8'h00))
        |-> (count_out == 8'hFF)
    );

    // Single-step up counting increments by one.
    check_up_single_step: assert property (
        @(posedge clk) disable iff (!rst)
        (!$initstate && $past(rst) && $past(enable) &&
         ($past(count_dir) == 1'b0) && ($past(dual_count) == 1'b0))
        |-> (count_out == ($past(count_out) + 8'h01))
    );

    // Single-step down counting decrements by one.
    check_down_single_step: assert property (
        @(posedge clk) disable iff (!rst)
        (!$initstate && $past(rst) && $past(enable) &&
         ($past(count_dir) == 1'b1) && ($past(dual_count) == 1'b0))
        |-> (count_out == ($past(count_out) - 8'h01))
    );

    // Dual-step up counting increments by two except at 8'hFF.
    check_up_dual_step: assert property (
        @(posedge clk) disable iff (!rst)
        (!$initstate && $past(rst) && $past(enable) &&
         ($past(count_dir) == 1'b0) && ($past(dual_count) == 1'b1) &&
         ($past(count_out) != 8'hFF))
        |-> (count_out == ($past(count_out) + 8'h02))
    );

    // Dual-step down counting decrements by two except at 8'h00.
    check_down_dual_step: assert property (
        @(posedge clk) disable iff (!rst)
        (!$initstate && $past(rst) && $past(enable) &&
         ($past(count_dir) == 1'b1) && ($past(dual_count) == 1'b1) &&
         ($past(count_out) != 8'h00))
        |-> (count_out == ($past(count_out) - 8'h02))
    );

endmodule