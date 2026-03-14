module parity_generator_sva (
    input logic CLK,
    input logic [7:0] in,
    input logic parity
);
    // Parity equals XOR reduction of in masked by 1.
    check_parity_definition: assert property (
        @(posedge CLK) parity == ((^in) & 1'b1)
    );

    // If input is stable, parity must remain stable.
    check_stability_when_input_stable: assert property (
        @(posedge CLK) $stable(in) |-> $stable(parity)
    );

    // Change in parity equals parity of the input delta.
    check_parity_delta_matches_input_delta: assert property (
        @(posedge CLK) (parity ^ $past(parity)) == ((^(in ^ $past(in))) & 1'b1)
    );

    // A single-bit flip in input must toggle parity.
    check_parity_toggles_on_onebit_flip: assert property (
        @(posedge CLK) $onehot(in ^ $past(in)) |-> (parity != $past(parity))
    );
endmodule