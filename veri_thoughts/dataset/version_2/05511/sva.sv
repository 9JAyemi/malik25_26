module decoder_4to16_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [15:0] Y
);

    // Any fully known input decodes to the matching one-hot output.
    check_decode_mapping_known: assert property (
        @(posedge clk) !$isunknown(A) |-> (Y === (16'h0001 << A))
    );

    // Any input containing X or Z drives the default zero output.
    check_default_zero_for_unknown_input: assert property (
        @(posedge clk) $isunknown(A) |-> (Y === 16'h0000)
    );

    // Any fully known input produces exactly one asserted output bit.
    check_onehot_for_known_input: assert property (
        @(posedge clk) !$isunknown(A) |-> $onehot(Y)
    );

    // A zero output can only occur when the input falls through the default case.
    check_zero_output_only_for_unknown_input: assert property (
        @(posedge clk) (Y === 16'h0000) |-> $isunknown(A)
    );

    // If the sampled input is unchanged, the sampled output is unchanged.
    check_output_stable_when_input_stable: assert property (
        @(posedge clk) (!$isunknown(A) && !$isunknown($past(A)) && (A == $past(A))) |-> (Y == $past(Y))
    );

endmodule