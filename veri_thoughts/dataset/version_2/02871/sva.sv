module setting_reg_sva
  #(parameter my_addr = 0,
    parameter width = 32,
    parameter at_reset = 32'd0)
(
    input logic clk,
    input logic rst,
    input logic strobe,
    input logic [7:0] addr,
    input logic [31:0] in,
    input logic [width-1:0] out,
    input logic changed
);

    // After a cycle with rst asserted, outputs must hold reset values.
    check_reset_state_after_rst: assert property (
        @(posedge clk) disable iff (rst)
            $past(rst) |-> (out == at_reset) && (changed == 1'b0)
    );

    // A write hit last cycle updates out to the previous in[width-1:0].
    check_write_updates_out: assert property (
        @(posedge clk) disable iff (rst)
            $past(!rst && strobe && (my_addr == addr)) |-> (out == $past(in[width-1:0]))
    );

    // A write hit last cycle sets changed HIGH now.
    check_write_sets_changed: assert property (
        @(posedge clk) disable iff (rst)
            $past(!rst && strobe && (my_addr == addr)) |-> (changed == 1'b1)
    );

    // With no write last cycle (and not in reset), out holds its previous value.
    check_hold_out_no_write: assert property (
        @(posedge clk) disable iff (rst)
            $past(!rst && !(strobe && (my_addr == addr))) |-> (out == $past(out))
    );

    // With no write last cycle (and not in reset), changed is LOW now.
    check_clears_changed_no_write: assert property (
        @(posedge clk) disable iff (rst)
            $past(!rst && !(strobe && (my_addr == addr))) |-> (changed == 1'b0)
    );

    // A strobe with address mismatch last cycle does not update out.
    check_mismatch_strobe_holds_out: assert property (
        @(posedge clk) disable iff (rst)
            $past(!rst && strobe && (my_addr != addr)) |-> (out == $past(out))
    );

    // A strobe with address mismatch last cycle keeps changed LOW.
    check_mismatch_strobe_clears_changed: assert property (
        @(posedge clk) disable iff (rst)
            $past(!rst && strobe && (my_addr != addr)) |-> (changed == 1'b0)
    );

    // If changed is HIGH now, the previous cycle must have been a write hit.
    check_changed_implies_prev_write: assert property (
        @(posedge clk) disable iff (rst)
            changed |-> $past(!rst && strobe && (my_addr == addr))
    );

    // out can only change due to a reset last cycle or a write hit last cycle.
    check_out_changes_only_on_write_or_reset: assert property (
        @(posedge clk) disable iff (rst)
            $changed(out) |-> ($past(rst) || $past(!rst && strobe && (my_addr == addr)))
    );

    // If there was a write last cycle and no write this cycle, changed must be LOW now (single-cycle pulse).
    check_changed_pulse_no_back_to_back: assert property (
        @(posedge clk) disable iff (rst)
            ($past(!rst && strobe && (my_addr == addr)) && !(strobe && (my_addr == addr))) |-> (changed == 1'b0)
    );

endmodule