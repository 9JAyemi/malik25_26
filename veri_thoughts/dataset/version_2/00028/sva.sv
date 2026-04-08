module top_module_sva (
    input logic CLK,
    input logic UP_DOWN,
    input logic RESET,
    input logic EN,
    input logic select,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] OUT1,
    input logic [7:0] OUT2
);

    // After a sampled reset, the counter output is zero on the next clock.
    check_counter_clears_after_reset: assert property (
        @(posedge CLK) RESET |=> (OUT1 == 4'h0)
    );

    // A zero counter value stays at zero when counting is disabled.
    check_counter_zero_holds_when_disabled: assert property (
        @(posedge CLK) disable iff (RESET)
        (!EN && (OUT1 == 4'h0)) |=> (OUT1 == 4'h0)
    );

    // Incrementing from 4'hF wraps the 4-bit counter back to zero.
    check_counter_wraps_on_increment_from_max: assert property (
        @(posedge CLK) disable iff (RESET)
        (EN && UP_DOWN && (OUT1 == 4'hF)) |=> (OUT1 == 4'h0)
    );

    // OUT2 always equals the product of A and B.
    check_multiplier_matches_ab_product: assert property (
        @(posedge CLK) disable iff (RESET)
        (OUT2 == (A * B))
    );

    // A zero multiplier operand forces the product to zero.
    check_multiplier_zero_operand_gives_zero: assert property (
        @(posedge CLK) disable iff (RESET)
        ((A == 4'h0) || (B == 4'h0)) |-> (OUT2 == 8'h00)
    );

    // A value of one on A passes B through the multiplier.
    check_multiplier_a_one_passes_b: assert property (
        @(posedge CLK) disable iff (RESET)
        (A == 4'h1) |-> (OUT2 == {4'b0000, B})
    );

    // A value of one on B passes A through the multiplier.
    check_multiplier_b_one_passes_a: assert property (
        @(posedge CLK) disable iff (RESET)
        (B == 4'h1) |-> (OUT2 == {4'b0000, A})
    );

    // Changing select alone does not change the product.
    check_select_change_does_not_change_product: assert property (
        @(posedge CLK) disable iff (RESET)
        ($changed(select) && $stable(A) && $stable(B)) |-> (OUT2 == $past(OUT2))
    );

endmodule