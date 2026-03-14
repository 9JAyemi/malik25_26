module INV4BITS_sva (
    // DUT ports
    input logic [3:0] in,
    input logic [3:0] out,
    // Sampling clock for assertions (RTL is combinational; no reset present)
    input logic CLK
);
    // Out equals bitwise NOT of in.
    check_inversion_vector: assert property (
        @(posedge CLK) out == ~in
    );

    // XOR of in and out is all ones.
    check_xor_all_ones: assert property (
        @(posedge CLK) (in ^ out) == 4'hF
    );

    // OR of in and out is all ones.
    check_or_all_ones: assert property (
        @(posedge CLK) (in | out) == 4'hF
    );

    // AND of in and out is zero.
    check_and_zero: assert property (
        @(posedge CLK) (in & out) == 4'h0
    );

    // Sum of in and out is 0xF.
    check_sum_all_ones: assert property (
        @(posedge CLK) (in + out) == 4'hF
    );

    // If input is stable, output remains stable.
    check_stability_if_input_stable: assert property (
        @(posedge CLK) $stable(in) |-> $stable(out)
    );

    // Input and output toggle masks match across cycles.
    check_toggle_mask_matches: assert property (
        @(posedge CLK) disable iff ($initstate) ((in ^ $past(in)) == (out ^ $past(out)))
    );
endmodule