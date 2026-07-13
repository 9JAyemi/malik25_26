module ripple_decoder_adder_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic Cin,
    input logic [3:0] Sum,
    input logic Cout,
    input logic [15:0] O
);
    // Adder outputs equal A + B + Cin (sum and carry)
    check_adder_sum_and_carry: assert property (
        @(posedge clk) {Cout, Sum} == (A + B + Cin)
    );

    // LSB sum bit is XOR of A[0], B[0], and Cin
    check_sum0_xor: assert property (
        @(posedge clk) Sum[0] == (A[0] ^ B[0] ^ Cin)
    );

    // Carry-out equals overflow of 4-bit addition
    check_cout_overflow: assert property (
        @(posedge clk) Cout == ((A + B + Cin) > 5'd15)
    );

    // Decoder output equals 1 shifted by Sum[3:2]
    check_decoder_mapping_shift: assert property (
        @(posedge clk) O == (16'h0001 << Sum[3:2])
    );

    // Decoder output is exactly one-hot
    check_decoder_onehot: assert property (
        @(posedge clk) $onehot(O)
    );

    // Upper decoder bits are zero
    check_decoder_upper_zero: assert property (
        @(posedge clk) O[15:4] == 12'h000
    );

    // If primary inputs hold, outputs hold (combinational behavior)
    check_outputs_hold_when_inputs_hold: assert property (
        @(posedge clk) $past(1'b1) && $stable({A,B,Cin}) |-> $stable({Sum,Cout,O})
    );

    // If Sum[3:2] holds, O holds (direct decode of Sum[3:2])
    check_o_stable_when_sum_msb_stable: assert property (
        @(posedge clk) $past(1'b1) && $stable(Sum[3:2]) |-> $stable(O)
    );

    // If Sum[3:2] changes, O changes accordingly
    check_o_changes_with_sum_msb_change: assert property (
        @(posedge clk) $past(1'b1) && (Sum[3:2] != $past(Sum[3:2])) |-> (O != $past(O))
    );
endmodule