module dual_d_flip_flop_sva (
    input logic clk,
    input logic reset,
    input logic d_in,
    output logic d_out_1,
    output logic d_out_2
);
    // Reset behavior: Both outputs should be LOW at reset
    reset_behavior: assert property (
        @(posedge clk) !reset |-> (d_out_1 == 1'b0) && (d_out_2 == 1'b0)
    );

    // d_out_1 should always be equal to d_in
    d_out_1_behavior: assert property (
        @(posedge clk) disable iff (!reset) d_out_1 == d_in
    );

    // d_out_2 should always be equal to the toggle of d_out_1 and d_in
    d_out_2_behavior: assert property (
        @(posedge clk) disable iff (!reset) d_out_2 == (d_out_1 ^ d_in)
    );

    // d_ff_1 should always be equal to d_in
    d_ff_1_behavior: assert property (
        @(posedge clk) disable iff (!reset) d_ff_1 == d_in
    );

    // d_ff_2 should always be equal to the toggle of d_out_1 and d_in
    d_ff_2_behavior: assert property (
        @(posedge clk) disable iff (!reset) d_ff_2 == (d_out_1 ^ d_in)
    );

    // Toggle signal should be equal to the XOR of d_out_1 and d_in
    toggle_behavior: assert property (
        @(posedge clk) disable iff (!reset) toggle == (d_out_1 ^ d_in)
    );

    // d_out_1 should not change when reset is active
    d_out_1_reset: assert property (
        @(posedge clk) !reset |-> ##1 d_out_1 == d_out_1
    );

    // d_out_2 should not change when reset is active
    d_out_2_reset: assert property (
        @(posedge clk) !reset |-> ##1 d_out_2 == d_out_2
    );

    // d_ff_1 should not change when reset is active
    d_ff_1_reset: assert property (
        @(posedge clk) !reset |-> ##1 d_ff_1 == d_ff_1
    );

    // d_ff_2 should not change when reset is active
    d_ff_2_reset: assert property (
        @(posedge clk) !reset |-> ##1 d_ff_2 == d_ff_2
    );

    // Toggle signal should not change when reset is active
    toggle_reset: assert property (
        @(posedge clk) !reset |-> ##1 toggle == toggle
    );
endmodule