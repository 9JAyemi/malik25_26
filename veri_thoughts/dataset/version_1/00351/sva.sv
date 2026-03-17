module nfa_accept_samples_generic_hw_mul_8ns_6ns_14_2_MAC2S_1_sva (
    input logic clk,
    input logic ce,
    input logic [7:0] a,
    input logic [5:0] b,
    input logic [13:0] p
);

    // When enabled, p captures the current unsigned product on the next cycle.
    check_capture_product: assert property (
        @(posedge clk) ce |=> p == ($past(a) * $past(b))
    );

    // When disabled, p holds its previous value.
    check_hold_when_ce_low: assert property (
        @(posedge clk) !ce |=> p == $past(p)
    );

    // A zero operand produces a zero result when captured.
    check_zero_operand_result: assert property (
        @(posedge clk) ce && ((a == 8'd0) || (b == 6'd0)) |=> p == 14'd0
    );

    // Multiplying by one on b passes a through when captured.
    check_multiply_by_one_on_b: assert property (
        @(posedge clk) ce && (b == 6'd1) |=> p == {6'd0, $past(a)}
    );

    // Multiplying by one on a passes b through when captured.
    check_multiply_by_one_on_a: assert property (
        @(posedge clk) ce && (a == 8'd1) |=> p == {8'd0, $past(b)}
    );

    // Maximum operands produce the maximum reachable product when captured.
    check_max_operand_product: assert property (
        @(posedge clk) ce && (a == 8'hff) && (b == 6'h3f) |=> p == 14'd16065
    );

endmodule