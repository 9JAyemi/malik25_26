module barrel_shifter_sva (
    input logic CLK,
    input logic [3:0] A,
    input logic [1:0] B,
    input logic [3:0] Y
);
    // B==00: pass-through
    check_b00_passthrough: assert property (
        @(posedge CLK) (B == 2'b00) |-> (Y == A)
    );

    // B==01: left shift by 1 with zero-fill on LSB
    check_b01_left_shift1: assert property (
        @(posedge CLK) (B == 2'b01) |-> (Y == {A[2:0], 1'b0})
    );

    // B==10: right shift by 1 with zero-fill on MSB
    check_b10_right_shift1: assert property (
        @(posedge CLK) (B == 2'b10) |-> (Y == {1'b0, A[3:1]})
    );

    // B==11: right shift by 2 with zero-fill on top two bits
    check_b11_right_shift2: assert property (
        @(posedge CLK) (B == 2'b11) |-> (Y == {2'b00, A[3:2]})
    );

    // For B==01, LSB must be zero
    check_b01_lsb_zero: assert property (
        @(posedge CLK) (B == 2'b01) |-> (Y[0] == 1'b0)
    );

    // For B==10, MSB must be zero
    check_b10_msb_zero: assert property (
        @(posedge CLK) (B == 2'b10) |-> (Y[3] == 1'b0)
    );

    // For B==11, top two bits must be zero
    check_b11_two_msb_zero: assert property (
        @(posedge CLK) (B == 2'b11) |-> (Y[3:2] == 2'b00)
    );

    // If A and B don't change, Y must not change
    check_output_stable_when_inputs_stable: assert property (
        @(posedge CLK) $stable({A, B}) |-> $stable(Y)
    );
endmodule