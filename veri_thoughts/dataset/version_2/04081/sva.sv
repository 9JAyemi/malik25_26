module bitwise_and_sva (
    input logic [3:0] in1,
    input logic [3:0] in2,
    input logic [3:0] out,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);

    // The output vector equals the bitwise AND of the two input vectors.
    check_out_matches_bitwise_and: assert property (
        @($global_clock) out == (in1 & in2)
    );

    // Output bit 0 equals the AND of input bit 0.
    check_out_bit0_matches_inputs: assert property (
        @($global_clock) out[0] == (in1[0] & in2[0])
    );

    // Output bit 1 equals the AND of input bit 1.
    check_out_bit1_matches_inputs: assert property (
        @($global_clock) out[1] == (in1[1] & in2[1])
    );

    // Output bit 2 equals the AND of input bit 2.
    check_out_bit2_matches_inputs: assert property (
        @($global_clock) out[2] == (in1[2] & in2[2])
    );

    // Output bit 3 equals the AND of input bit 3.
    check_out_bit3_matches_inputs: assert property (
        @($global_clock) out[3] == (in1[3] & in2[3])
    );

    // Output bit 0 stays stable when its corresponding inputs stay stable.
    check_out_bit0_stable_when_inputs_stable: assert property (
        @($global_clock) ($stable(in1[0]) && $stable(in2[0])) |-> $stable(out[0])
    );

    // Output bit 1 stays stable when its corresponding inputs stay stable.
    check_out_bit1_stable_when_inputs_stable: assert property (
        @($global_clock) ($stable(in1[1]) && $stable(in2[1])) |-> $stable(out[1])
    );

    // Output bit 2 stays stable when its corresponding inputs stay stable.
    check_out_bit2_stable_when_inputs_stable: assert property (
        @($global_clock) ($stable(in1[2]) && $stable(in2[2])) |-> $stable(out[2])
    );

    // Output bit 3 stays stable when its corresponding inputs stay stable.
    check_out_bit3_stable_when_inputs_stable: assert property (
        @($global_clock) ($stable(in1[3]) && $stable(in2[3])) |-> $stable(out[3])
    );

endmodule