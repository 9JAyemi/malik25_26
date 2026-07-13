module DLL_sva (
    input logic       ref_clk,
    input logic       feedback_clk,
    input logic [7:0] delay,
    input logic       out_clk,
    input logic [7:0] delay_reg,
    input logic [7:0] error,
    input logic [7:0] error_filtered,
    input logic [7:0] error_integrated,
    input logic [7:0] error_integrated_next,
    input logic [7:0] error_filtered_next,
    input logic [7:0] phase_detector_out,
    input logic [7:0] delay_line_out,
    input logic [7:0] out_clk_reg,
    input logic [7:0] out_clk_next
);

    // delay_reg samples delay on ref_clk.
    check_delay_reg_captures_delay: assert property (
        @(posedge ref_clk) 1'b1 |=> (delay_reg == $past(delay))
    );

    // error samples phase_detector_out on ref_clk.
    check_error_captures_phase_detector: assert property (
        @(posedge ref_clk) 1'b1 |=> (error == $past(phase_detector_out))
    );

    // error_filtered samples error_filtered_next on ref_clk.
    check_error_filtered_updates: assert property (
        @(posedge ref_clk) 1'b1 |=> (error_filtered == $past(error_filtered_next))
    );

    // error_integrated samples error_integrated_next on ref_clk.
    check_error_integrated_updates: assert property (
        @(posedge ref_clk) 1'b1 |=> (error_integrated == $past(error_integrated_next))
    );

    // out_clk_reg samples out_clk_next on ref_clk.
    check_out_clk_reg_updates: assert property (
        @(posedge ref_clk) 1'b1 |=> (out_clk_reg == $past(out_clk_next))
    );

    // out_clk is the truncated LSB of out_clk_reg.
    check_out_clk_matches_out_clk_reg_lsb: assert property (
        @(posedge ref_clk) (out_clk == out_clk_reg[0])
    );

    // delay_line_out follows the final feedback-clock assignment controlled by delay_reg[0].
    check_delay_line_out_final_assignment: assert property (
        @(posedge feedback_clk) 1'b1 |=> (delay_line_out == ($past(delay_reg[0]) ? $past(delay_line_out) : 8'h01))
    );

    // phase_detector_out is delay_line_out XORed with a logic 1 at feedback_clk edges.
    check_phase_detector_out_xor: assert property (
        @(posedge feedback_clk) 1'b1 |=> (phase_detector_out == ($past(delay_line_out) ^ 8'h01))
    );

    // error_filtered_next is the averaged sum of error_filtered and error.
    check_error_filtered_next_computation: assert property (
        @(posedge feedback_clk) 1'b1 |=> (error_filtered_next == (($past(error_filtered) + $past(error)) >> 1))
    );

    // error_integrated_next accumulates error_integrated and error_filtered_next.
    check_error_integrated_next_computation: assert property (
        @(posedge feedback_clk) 1'b1 |=> (error_integrated_next == ($past(error_integrated) + $past(error_filtered_next)))
    );

    // out_clk_next follows the final feedback-clock assignment controlled by delay_reg[0].
    check_out_clk_next_final_assignment: assert property (
        @(posedge feedback_clk) 1'b1 |=> (out_clk_next == ($past(delay_reg[0]) ? $past(out_clk_reg) : $past(delay_line_out)))
    );

endmodule