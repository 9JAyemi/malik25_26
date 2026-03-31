module top_module_sva (
    input logic [31:0] a,
    input logic [31:0] b,
    input logic sub,
    input logic clk,
    input logic [31:0] result
);

    // Result matches the selected 16-bit sum from the RTL.
    check_result_matches_selected_sum: assert property (
        @(posedge clk) result == (sub ? {16'b0, a[15:0] + b[15:0]} : {16'b0, a[15:0]})
    );

    // In add mode, result is the low 16 bits of a[15:0] plus b[15:0].
    check_add_mode_result: assert property (
        @(posedge clk) !sub |-> (result == {16'b0, a[15:0] + b[15:0]})
    );

    // In subtract mode, result is zero because the low 16-bit sum is zero.
    check_sub_mode_result: assert property (
        @(posedge clk) sub |-> (result == 32'h00000000)
    );

    // With unchanged a[15:0] and b[15:0], result stays unchanged.
    check_result_stable_when_low_half_inputs_stable: assert property (
        @(posedge clk) ($stable(a[15:0]) && $stable(b[15:0])) |-> $stable(result)
    );

    // With unchanged a[15:0], result stays unchanged regardless of sub.
    check_result_stable_when_a_low_half_stable: assert property (
        @(posedge clk) ($stable(a[15:0]) && $stable(sub)) |-> $stable(result)
    );

    // With unchanged b[15:0], result stays unchanged regardless of sub.
    check_result_stable_when_b_low_half_stable: assert property (
        @(posedge clk) ($stable(b[15:0]) && $stable(sub)) |-> $stable(result)
    );

    // With unchanged sub, result stays unchanged regardless of a[15:0] or b[15:0].
    check_result_stable_when_sub_stable: assert property (
        @(posedge clk) $stable(sub) |-> $stable(result)
    );

    // If a[15:0] is zero, result is zero in both modes.
    check_zero_a_low_half_zero_result: assert property (
        @(posedge clk) (a[15:0] == 16'h0000) |-> (result == 32'h00000000)
    );

    // If b[15:0] is zero, result matches a[15:0] in add mode.
    check_zero_b_low_half_add_mode_result: assert property (
        @(posedge clk) (!sub && (b[15:0] == 16'h0000)) |-> (result == {16'b0, a[15:0]})
    );

    // In add mode, equal low halves cancel to zero.
    check_add_mode_equal_low_halves_cancel: assert property (
        @(posedge clk) (!sub && (a[15:0] == b[15:0])) |-> (result == 32'h00000000)
    );

    // In add mode, adding zero on b leaves a[15:0] unchanged.
    check_add_mode_zero_b_passthrough: assert property (
        @(posedge clk) (!sub && (b[15:0] == 16'h0000)) |-> (result == {16'b0, a[15:0]})
    );

    // In add mode, adding zero on a leaves b[15:0] unchanged.
    check_add_mode_zero_a_passthrough: assert property (
        @(posedge clk) (!sub && (a[15:0] == 16'h0000)) |-> (result == {16'b0, b[15:0]})
    );

endmodule