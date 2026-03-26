module gtwizard_ultrascale_v1_7_1_bit_synchronizer_sva (
    input logic clk_in,
    input logic i_in,
    input logic o_out,
    input logic i_in_meta,
    input logic i_in_sync1,
    input logic i_in_sync2,
    input logic i_in_sync3,
    input logic i_in_out
);

    // First stage samples the input.
    check_meta_captures_input: assert property (
        @(posedge clk_in) 1'b1 |=> (i_in_meta == $past(i_in))
    );

    // Second stage samples the first stage.
    check_sync1_captures_meta: assert property (
        @(posedge clk_in) 1'b1 |=> (i_in_sync1 == $past(i_in_meta))
    );

    // Third stage samples the second stage.
    check_sync2_captures_sync1: assert property (
        @(posedge clk_in) 1'b1 |=> (i_in_sync2 == $past(i_in_sync1))
    );

    // Fourth stage samples the third stage.
    check_sync3_captures_sync2: assert property (
        @(posedge clk_in) 1'b1 |=> (i_in_sync3 == $past(i_in_sync2))
    );

    // Final register samples the fourth stage.
    check_out_reg_captures_sync3: assert property (
        @(posedge clk_in) 1'b1 |=> (i_in_out == $past(i_in_sync3))
    );

    // Output wire mirrors the final register.
    check_output_matches_out_reg: assert property (
        @(posedge clk_in) (o_out == i_in_out)
    );

    // Second stage is a two-cycle delayed copy of the input.
    check_sync1_two_cycle_delay: assert property (
        @(posedge clk_in) 1'b1 |-> ##2 (i_in_sync1 == $past(i_in,2))
    );

    // Third stage is a three-cycle delayed copy of the input.
    check_sync2_three_cycle_delay: assert property (
        @(posedge clk_in) 1'b1 |-> ##3 (i_in_sync2 == $past(i_in,3))
    );

    // Fourth stage is a four-cycle delayed copy of the input.
    check_sync3_four_cycle_delay: assert property (
        @(posedge clk_in) 1'b1 |-> ##4 (i_in_sync3 == $past(i_in,4))
    );

    // Output is a five-cycle delayed copy of the input.
    check_output_five_cycle_delay: assert property (
        @(posedge clk_in) 1'b1 |-> ##5 (o_out == $past(i_in,5))
    );

endmodule