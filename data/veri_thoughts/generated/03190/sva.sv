module number_in_sva (
    input logic [31:0] num_a,
    input logic [31:0] num_b,
    input logic [31:0] result,
    input logic [4:0]  code,
    input logic        btnm,
    input logic [32:0] num_out,
    input logic [31:0] \new ,
    input logic [1:0]  state,
    input logic        b_state
);

    localparam [1:0] numA = 2'b00;
    localparam [1:0] numB = 2'b01;
    localparam [1:0] numC = 2'b10;

    // Pressing the button forces b_state high.
    check_button_latch_high_when_pressed: assert property (
        @($global_clock) btnm |-> (b_state == 1'b1)
    );

    // Releasing the button forces b_state low.
    check_button_latch_low_when_released: assert property (
        @($global_clock) !btnm |-> (b_state == 1'b0)
    );

    // State remains within the three implemented encodings.
    check_state_encoding_legal: assert property (
        @($global_clock) ((state == numA) || (state == numB) || (state == numC))
    );

    // Non-negative selected values clear the sign bit on num_out.
    check_output_sign_clear_for_nonnegative: assert property (
        @($global_clock) (\new [31] == 1'b0) |-> (num_out[32] == 1'b0)
    );

    // Negative selected values set the sign bit on num_out.
    check_output_sign_set_for_negative: assert property (
        @($global_clock) (\new [31] == 1'b1) |-> (num_out[32] == 1'b1)
    );

    // Non-negative selected values pass through unchanged.
    check_output_passthrough_for_nonnegative: assert property (
        @($global_clock) (\new [31] == 1'b0) |-> (num_out[31:0] == \new )
    );

    // Negative selected values are converted to magnitude form.
    check_output_magnitude_for_negative: assert property (
        @($global_clock) (\new [31] == 1'b1) |-> (num_out[31:0] == (32'd0 - \new ))
    );

endmodule