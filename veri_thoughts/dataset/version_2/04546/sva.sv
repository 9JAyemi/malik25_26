module pipelined_JC_counter_sva (
    input logic        clk,
    input logic        rst_n,
    input logic [3:0]  Q,
    input logic [63:0] shift_reg,
    input logic [3:0]  feedback
);

    // Feedback is the selected tap vector from shift_reg.
    check_feedback_taps: assert property (
        @(posedge clk) disable iff (!rst_n)
        feedback == {shift_reg[0], shift_reg[15], shift_reg[30], shift_reg[45]}
    );

    // Active-low reset clears the state and derived feedback by the next cycle.
    check_reset_clears_state: assert property (
        @(posedge clk)
        !rst_n |=> (shift_reg == 64'h0000000000000000) &&
                   (Q == 4'h0) &&
                   (feedback == 4'h0)
    );

    // The upper 60 bits of shift_reg take the prior lower 60 bits.
    check_shift_reg_upper_pipeline: assert property (
        @(posedge clk) disable iff (!rst_n)
        rst_n |=> (shift_reg[63:4] == $past(shift_reg[59:0]))
    );

    // The low nibble of shift_reg takes the prior feedback value.
    check_shift_reg_lower_pipeline: assert property (
        @(posedge clk) disable iff (!rst_n)
        rst_n |=> (shift_reg[3:0] == $past(feedback))
    );

    // Q captures the prior top nibble of shift_reg.
    check_q_captures_previous_top_nibble: assert property (
        @(posedge clk) disable iff (!rst_n)
        rst_n |=> (Q == $past(shift_reg[63:60]))
    );

    // A zero shift_reg keeps the machine at zero on the next active cycle.
    check_zero_shift_reg_holds_zero_state: assert property (
        @(posedge clk) disable iff (!rst_n)
        (shift_reg == 64'h0000000000000000) |=> (shift_reg == 64'h0000000000000000) &&
                                               (Q == 4'h0) &&
                                               (feedback == 4'h0)
    );

endmodule