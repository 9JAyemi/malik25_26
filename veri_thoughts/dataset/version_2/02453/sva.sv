module adder4_sva (
    input  logic        clk,
    input  logic [3:0]  A,
    input  logic [3:0]  B,
    input  logic        Cin,
    input  logic [3:0]  S,
    input  logic        Cout
);
    // Sum and carry implement 4-bit addition with carry-in.
    check_full_sum: assert property (
        @(posedge clk) {Cout, S} == (A + B + Cin)
    );

    // S equals lower 4 bits of A+B+Cin.
    check_s_lower_bits: assert property (
        @(posedge clk) S == (A + B + Cin)[3:0]
    );

    // Cout equals bit[4] (overflow) of A+B+Cin.
    check_cout_upper_bit: assert property (
        @(posedge clk) Cout == (A + B + Cin)[4]
    );

    // LSB sum equals XOR of A[0], B[0], and Cin.
    check_lsb_xor: assert property (
        @(posedge clk) S[0] == (A[0] ^ B[0] ^ Cin)
    );

    // If inputs are known, outputs are known.
    check_no_x_when_inputs_known: assert property (
        @(posedge clk) (!$isunknown({A, B, Cin})) |-> (!$isunknown({S, Cout}))
    );

    // With A=0 and B=0, result equals Cin and no carry.
    check_zero_operands: assert property (
        @(posedge clk) ((A == 4'd0) && (B == 4'd0)) |-> ((S == {3'b000, Cin}) && (Cout == 1'b0))
    );

    // With B=0 and Cin=0, S passes A and no carry.
    check_passthrough_A: assert property (
        @(posedge clk) ((B == 4'd0) && (Cin == 1'b0)) |-> ((S == A) && (Cout == 1'b0))
    );

    // With A=0 and Cin=0, S passes B and no carry.
    check_passthrough_B: assert property (
        @(posedge clk) ((A == 4'd0) && (Cin == 1'b0)) |-> ((S == B) && (Cout == 1'b0))
    );

    // With B = ~A and Cin=0, sum is 0xF and no carry.
    check_complement_no_cin: assert property (
        @(posedge clk) ((B == ~A) && (Cin == 1'b0)) |-> ((S == 4'hF) && (Cout == 1'b0))
    );

    // With B = ~A and Cin=1, sum is 0x0 and carry=1.
    check_complement_with_cin: assert property (
        @(posedge clk) ((B == ~A) && (Cin == 1'b1)) |-> ((S == 4'h0) && (Cout == 1'b1))
    );

    // If inputs are stable from cycle to cycle, outputs are stable.
    check_output_stable_when_inputs_stable: assert property (
        @(posedge clk) $stable({A, B, Cin}) |-> $stable({S, Cout})
    );
endmodule