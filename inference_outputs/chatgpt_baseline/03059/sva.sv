module top_module_sva (
    input logic        clk,
    input logic        reset,
    input logic [31:0] a,
    input logic [31:0] b,
    input logic        select,
    input logic [31:0] sum
);

    // A sampled reset leaves the registered output cleared on the next clock.
    check_reset_next_cycle_zero: assert property (
        @(posedge clk)
        reset |=> (sum == 32'h00000000)
    );

    // The output register captures the prior cycle's selected 32-bit result.
    check_registered_selected_result: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (sum == ($past(select) ? ($past(a) + (~$past(b))) : ($past(a) + $past(b))))
    );

    // With select low, the next sum is the prior cycle's 32-bit a+b result.
    check_registered_add_path: assert property (
        @(posedge clk) disable iff (reset)
        (!select) |=> (sum == ($past(a) + $past(b)))
    );

    // With select high, the next sum is the prior cycle's 32-bit a+~b result.
    check_registered_invert_b_path: assert property (
        @(posedge clk) disable iff (reset)
        select |=> (sum == ($past(a) + (~$past(b))))
    );

    // Adding zero on the normal path passes a through on the next cycle.
    check_add_zero_b_passthrough: assert property (
        @(posedge clk) disable iff (reset)
        (!select && (b == 32'h00000000)) |=> (sum == $past(a))
    );

    // Inverting all ones makes the alternate path pass a through on the next cycle.
    check_invert_all_ones_b_passthrough: assert property (
        @(posedge clk) disable iff (reset)
        (select && (b == 32'hFFFF_FFFF)) |=> (sum == $past(a))
    );

endmodule