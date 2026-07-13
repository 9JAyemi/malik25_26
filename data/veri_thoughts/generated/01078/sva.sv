module sky130_fd_sc_hdll__xor2_sva (
    input logic X,
    input logic A,
    input logic B
);
    // X equals A XOR B when A rises.
    check_x_equals_a_xor_b_on_posedge_A: assert property (
        @(posedge A) X === (A ^ B)
    );

    // X equals A XOR B when B rises.
    check_x_equals_a_xor_b_on_posedge_B: assert property (
        @(posedge B) X === (A ^ B)
    );

    // (X XOR B) equals A when A rises.
    check_x_xor_b_equals_a_on_posedge_A: assert property (
        @(posedge A) (X ^ B) === A
    );

    // (X XOR A) equals B when B rises.
    check_x_xor_a_equals_b_on_posedge_B: assert property (
        @(posedge B) (X ^ A) === B
    );

    // When A rises and B is 0, X must be 1.
    check_output_high_when_A_rises_and_B0: assert property (
        @(posedge A) (B === 1'b0) |-> (X === 1'b1)
    );

    // When A rises and B is 1, X must be 0.
    check_output_low_when_A_rises_and_B1: assert property (
        @(posedge A) (B === 1'b1) |-> (X === 1'b0)
    );

    // When B rises and A is 0, X must be 1.
    check_output_high_when_B_rises_and_A0: assert property (
        @(posedge B) (A === 1'b0) |-> (X === 1'b1)
    );

    // When B rises and A is 1, X must be 0.
    check_output_low_when_B_rises_and_A1: assert property (
        @(posedge B) (A === 1'b1) |-> (X === 1'b0)
    );
endmodule