module ones_counter_sva (
    input logic [3:0] in,
    input logic clk,
    input logic rst,
    input logic [2:0] out
);
    ///// Reset behavior /////
    // If reset was asserted in the previous cycle, out must be 0 now.
    check_reset_clears_out_next: assert property (
        @(posedge clk) $past(rst) |-> (out == 3'd0)
    );

    ///// Functional update /////
    // When not in reset in the previous cycle, out equals the previous cycle's sum of input bits.
    check_out_eq_prev_sum_when_prev_not_rst: assert property (
        @(posedge clk) disable iff (rst) $past(!rst) |-> (out == $past(in[0] + in[1] + in[2] + in[3]))
    );

    ///// Output range /////
    // out is always within 0..4.
    check_out_range: assert property (
        @(posedge clk) (out <= 3'd4)
    );

    ///// Specific input patterns /////
    // If previous input was 4'b0000 and not in reset, out is 0.
    check_prev_in_zero_results_zero: assert property (
        @(posedge clk) disable iff (rst) $past(!rst) && ($past(in) == 4'b0000) |-> (out == 3'd0)
    );

    // If previous input was one-hot and not in reset, out is 1.
    check_prev_in_onehot_results_one: assert property (
        @(posedge clk) disable iff (rst) $past(!rst) && $onehot($past(in)) |-> (out == 3'd1)
    );

    ///// Bit-level consequences /////
    // The LSB of out equals the parity (XOR) of previous inputs when not in reset.
    check_lsb_matches_parity: assert property (
        @(posedge clk) disable iff (rst) $past(!rst) |-> (out[0] == ^$past(in))
    );

    ///// Temporal consistency /////
    // If inputs were stable over the last two cycles (and not in reset), out does not change this cycle.
    check_out_stable_if_input_stable: assert property (
        @(posedge clk) disable iff (rst)
            $past(!rst) && $past(!rst,2) && ($past(in) == $past(in,2)) |-> (out == $past(out))
    );

    // If exactly one input bit toggled between the last two cycles (and not in reset), out changes by 1.
    check_one_bit_toggle_changes_by_one: assert property (
        @(posedge clk) disable iff (rst)
            $past(!rst) && $past(!rst,2) && $onehot($past(in) ^ $past(in,2))
            |-> ((out == $past(out) + 3'd1) || ($past(out) == out + 3'd1))
    );
endmodule