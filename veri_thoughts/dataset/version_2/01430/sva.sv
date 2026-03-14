module eight_bit_adder_sva (
    input logic clk,
    input logic [7:0] A,
    input logic [7:0] B,
    input logic Cin,
    input logic [7:0] S,
    input logic Cout
);
    // Analysis: no clock/reset in DUT; pure combinational 8-bit adder with carry-out.
    // Behavior: temp_sum = {0,A}+{0,B}+{0,Cin}; S = temp_sum[7:0]; Cout = temp_sum[8].
    // Assertions are sampled on an external clk.

    // The 9-bit result equals zero-extended A+B+Cin.
    check_full_sum_mapping: assert property (
        @(posedge clk) {Cout, S} == ({1'b0, A} + {1'b0, B} + {1'b0, Cin})
    );

    // S equals the lower 8 bits of the zero-extended sum.
    check_sum_lower_bits: assert property (
        @(posedge clk) S == (({1'b0, A} + {1'b0, B} + {1'b0, Cin})[7:0])
    );

    // Cout equals the MSB of the zero-extended sum.
    check_carry_out_bit: assert property (
        @(posedge clk) Cout == (({1'b0, A} + {1'b0, B} + {1'b0, Cin})[8])
    );

    // Cout reflects whether the zero-extended sum exceeds 255.
    check_cout_threshold_equivalence: assert property (
        @(posedge clk) Cout == (({1'b0, A} + {1'b0, B} + {1'b0, Cin}) >= 9'd256)
    );

    // With zero inputs, output sum and carry are zero.
    corner_zero_inputs: assert property (
        @(posedge clk) (A == 8'h00 && B == 8'h00 && Cin == 1'b0) |-> (S == 8'h00 && Cout == 1'b0)
    );

    // 0xFF + 0x00 + 1 -> 0x00 with carry.
    corner_ff_plus_zero_cin1: assert property (
        @(posedge clk) (A == 8'hFF && B == 8'h00 && Cin == 1'b1) |-> (S == 8'h00 && Cout == 1'b1)
    );

    // 0xFF + 0xFF + 0 -> 0xFE with carry.
    corner_ff_plus_ff_cin0: assert property (
        @(posedge clk) (A == 8'hFF && B == 8'hFF && Cin == 1'b0) |-> (S == 8'hFE && Cout == 1'b1)
    );

    // 0xFF + 0xFF + 1 -> 0xFF with carry.
    corner_ff_plus_ff_cin1: assert property (
        @(posedge clk) (A == 8'hFF && B == 8'hFF && Cin == 1'b1) |-> (S == 8'hFF && Cout == 1'b1)
    );

    // If inputs are stable, outputs remain stable (pure combinational behavior).
    stable_inputs_hold_outputs: assert property (
        @(posedge clk) ($stable(A) && $stable(B) && $stable(Cin)) |-> $stable({Cout, S})
    );

    // Rising Cin with A and B stable increments the 9-bit result by 1.
    cin_rise_increments: assert property (
        @(posedge clk) ($rose(Cin) && $stable(A) && $stable(B)) |-> ({Cout, S} == $past({Cout, S}) + 9'd1)
    );

    // Falling Cin with A and B stable decrements the 9-bit result by 1.
    cin_fall_decrements: assert property (
        @(posedge clk) ($fell(Cin) && $stable(A) && $stable(B)) |-> ({Cout, S} == $past({Cout, S}) - 9'd1)
    );

endmodule