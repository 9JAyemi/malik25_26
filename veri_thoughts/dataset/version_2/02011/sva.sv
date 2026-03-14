module prog_counter2_sva (
    input logic [0:31] out_pc,
    input logic rst,
    input logic clk
);
    // Clock: clk (posedge). Reset: rst (active-high, synchronous).
    // Sequential behavior: out_pc resets to 0, else increments by 4 each clk.

    // Reset drives out_pc to zero on each clock with rst=1.
    check_reset_forces_zero: assert property (
        @(posedge clk) rst |-> (out_pc == 32'd0)
    );

    // First cycle after reset deassertion increments by 4.
    check_plus4_first_after_deassert: assert property (
        @(posedge clk) $rose(!rst) |-> (out_pc == $past(out_pc) + 32'd4)
    );

    // On consecutive run cycles (no reset), out_pc increments by 4.
    check_plus4_steady_run: assert property (
        @(posedge clk) disable iff (rst) $past(!rst) |-> (out_pc == $past(out_pc) + 32'd4)
    );

    // Lowest two bits are 00 on the first cycle after reset deassertion.
    check_lsb00_first_after_deassert: assert property (
        @(posedge clk) $rose(!rst) |-> (out_pc[30] == 1'b0) && (out_pc[31] == 1'b0)
    );

    // Lowest two bits remain unchanged across consecutive run cycles.
    check_lsbs_unchanged_while_running: assert property (
        @(posedge clk) disable iff (rst) $past(!rst) |-> (out_pc[30] == $past(out_pc[30])) && (out_pc[31] == $past(out_pc[31]))
    );

    // Wrap to zero from 32'hFFFF_FFFC on the next run cycle.
    check_wrap_to_zero_at_max: assert property (
        @(posedge clk) disable iff (rst) ($past(!rst) && ($past(out_pc) == 32'hFFFF_FFFC)) |-> (out_pc == 32'h00000000)
    );

    // When not wrapping (prev != 0xFFFF_FFFC), value strictly increases on run cycles.
    check_strict_increase_no_wrap: assert property (
        @(posedge clk) disable iff (rst) ($past(!rst) && ($past(out_pc) != 32'hFFFF_FFFC)) |-> (out_pc > $past(out_pc))
    );

endmodule