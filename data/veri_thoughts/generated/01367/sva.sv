module signed_output_sva (
    input signed [31:0] input_value,
    input signed [15:0] output_value,
    input signed sign_flag
);
    ///// Functional checks /////
    // output_value equals the upper 16 bits of input_value (arithmetic right shift by 16).
    check_output_equals_upper_16: assert property (
        @(posedge input_value[0]) output_value == input_value[31:16]
    );

    // sign_flag reflects (input_value < 0).
    check_sign_flag_matches_negative: assert property (
        @(posedge input_value[0]) sign_flag == (input_value < 0)
    );

    // sign_flag equals MSB of input_value.
    check_sign_flag_equals_msb: assert property (
        @(posedge input_value[0]) sign_flag == input_value[31]
    );

    // output_value MSB equals sign_flag.
    check_output_msb_matches_sign_flag: assert property (
        @(posedge input_value[0]) output_value[15] == sign_flag
    );

    // If high 16 bits are zero, output_value is zero and sign_flag is 0.
    check_zero_highhalf_zero_out: assert property (
        @(posedge input_value[0]) (input_value[31:16] == 16'h0000) |-> ((output_value == 16'h0000) && (sign_flag == 1'b0))
    );

    // If high 16 bits are all ones, output_value is 0xFFFF and sign_flag is 1.
    check_allones_highhalf_allones_out: assert property (
        @(posedge input_value[0]) (input_value[31:16] == 16'hFFFF) |-> ((output_value == 16'hFFFF) && (sign_flag == 1'b1))
    );

    // Non-negative input implies sign_flag is 0.
    check_nonneg_implies_sign0: assert property (
        @(posedge input_value[0]) (input_value >= 0) |-> (sign_flag == 1'b0)
    );

    // Negative input implies sign_flag is 1.
    check_neg_implies_sign1: assert property (
        @(posedge input_value[0]) (input_value < 0) |-> (sign_flag == 1'b1)
    );
endmodule