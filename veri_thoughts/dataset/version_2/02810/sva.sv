module xor_4bit_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] Y
);
    ///// Functional correctness /////
    // Y equals bitwise XOR of A and B.
    check_y_equals_bitwise_xor: assert property (
        @(posedge clk) Y === (A ^ B)
    );
    // Y[0] equals A[0] XOR B[0].
    check_y0_is_xor: assert property (
        @(posedge clk) Y[0] === (A[0] ^ B[0])
    );
    // Y[1] equals A[1] XOR B[1].
    check_y1_is_xor: assert property (
        @(posedge clk) Y[1] === (A[1] ^ B[1])
    );
    // Y[2] equals A[2] XOR B[2].
    check_y2_is_xor: assert property (
        @(posedge clk) Y[2] === (A[2] ^ B[2])
    );
    // Y[3] equals A[3] XOR B[3].
    check_y3_is_xor: assert property (
        @(posedge clk) Y[3] === (A[3] ^ B[3])
    );

    ///// Stability /////
    // If A and B are stable, Y must be stable.
    check_y_stable_when_inputs_stable: assert property (
        @(posedge clk) ($stable(A) && $stable(B)) |-> $stable(Y)
    );

    ///// Bitwise independence /////
    // Changing only bit 0 inputs cannot affect Y[3:1].
    check_high_bits_stable_on_bit0_input_change: assert property (
        @(posedge clk)
        (($changed(A[0]) || $changed(B[0])) && $stable(A[3:1]) && $stable(B[3:1])) |-> $stable(Y[3:1])
    );
    // Changing only bit 1 inputs cannot affect Y[{3:2,0}].
    check_other_bits_stable_on_bit1_input_change: assert property (
        @(posedge clk)
        (($changed(A[1]) || $changed(B[1])) && $stable({A[3:2],A[0]}) && $stable({B[3:2],B[0]})) |-> $stable({Y[3:2],Y[0]})
    );
    // Changing only bit 2 inputs cannot affect Y[{3,1:0}].
    check_other_bits_stable_on_bit2_input_change: assert property (
        @(posedge clk)
        (($changed(A[2]) || $changed(B[2])) && $stable({A[3],A[1:0]}) && $stable({B[3],B[1:0]})) |-> $stable({Y[3],Y[1:0]})
    );
    // Changing only bit 3 inputs cannot affect Y[2:0].
    check_low_bits_stable_on_bit3_input_change: assert property (
        @(posedge clk)
        (($changed(A[3]) || $changed(B[3])) && $stable(A[2:0]) && $stable(B[2:0])) |-> $stable(Y[2:0])
    );
endmodule