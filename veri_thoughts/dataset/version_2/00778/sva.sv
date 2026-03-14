module bin2gray_sva (
    input logic clk,
    input logic [3:0] in,
    input logic [3:0] out
);
    ///// Functional mapping /////
    // out equals Gray transform of previous in on each clock.
    check_gray_vector_map: assert property (
        @(posedge clk) out == $past({in[3], in[3]^in[2], in[2]^in[1], in[1]^in[0]})
    );
    // out[3] equals previous in[3].
    check_msb_direct_map: assert property (
        @(posedge clk) out[3] == $past(in[3])
    );
    // out[2] equals previous in[3] XOR in[2].
    check_bit2_xor_map: assert property (
        @(posedge clk) out[2] == $past(in[3] ^ in[2])
    );
    // out[1] equals previous in[2] XOR in[1].
    check_bit1_xor_map: assert property (
        @(posedge clk) out[1] == $past(in[2] ^ in[1])
    );
    // out[0] equals previous in[1] XOR in[0].
    check_bit0_xor_map: assert property (
        @(posedge clk) out[0] == $past(in[1] ^ in[0])
    );

    ///// Inversion relations /////
    // Previous in[2] equals out[3] XOR out[2].
    check_recover_in2_from_out: assert property (
        @(posedge clk) (out[3] ^ out[2]) == $past(in[2])
    );
    // Previous in[1] equals out[2] XOR out[1].
    check_recover_in1_from_out: assert property (
        @(posedge clk) (out[2] ^ out[1]) == $past(in[1])
    );
    // Previous in[0] equals out[1] XOR out[0].
    check_recover_in0_from_out: assert property (
        @(posedge clk) (out[1] ^ out[0]) == $past(in[0])
    );

    ///// Temporal consistency /////
    // If in was unchanged across the two prior cycles, out is unchanged across the last cycle.
    check_out_stable_when_prev_in_stable: assert property (
        @(posedge clk) ($past(in) == $past(in,2)) |-> (out == $past(out))
    );
    // If in increased by 1 between the two prior cycles, exactly one out bit toggled last cycle.
    check_gray_onebit_change_for_inc_by1: assert property (
        @(posedge clk) ($past(in) == ($past(in,2) + 4'd1)) |-> $onehot(out ^ $past(out))
    );
endmodule