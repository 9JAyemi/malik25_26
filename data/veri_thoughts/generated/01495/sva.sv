module ripple_adder_sva (
    input logic CLK,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic Cin,
    input logic [3:0] S,
    input logic Cout
);
    ///// Arithmetic correctness /////
    // Combined output equals zero-extended sum of A, B, and Cin.
    check_combined_sum: assert property (
        @(posedge CLK) {Cout, S} == ({1'b0, A} + {1'b0, B} + Cin)
    );

    // Lower 4 bits of the sum drive S.
    check_s_low_bits: assert property (
        @(posedge CLK) S == (({1'b0, A} + {1'b0, B} + Cin)[3:0])
    );

    // MSB of the sum drives Cout.
    check_carry_out_bit: assert property (
        @(posedge CLK) Cout == (({1'b0, A} + {1'b0, B} + Cin)[4])
    );

    ///// Input-conditional behaviors /////
    // With Cin=0, outputs equal A+B.
    check_no_carry_in_case: assert property (
        @(posedge CLK) (!Cin) |-> ({Cout, S} == ({1'b0, A} + {1'b0, B}))
    );

    // With Cin=1, outputs equal A+B+1.
    check_with_carry_in_case: assert property (
        @(posedge CLK) (Cin) |-> ({Cout, S} == ({1'b0, A} + {1'b0, B} + 5'd1))
    );

    // All zeros in => all zeros out.
    check_zero_case: assert property (
        @(posedge CLK) (A == 4'd0 && B == 4'd0 && Cin == 1'b0) |-> (S == 4'd0 && Cout == 1'b0)
    );

    // Max inputs with Cin=1 => S=0xF and Cout=1.
    check_max_case: assert property (
        @(posedge CLK) (A == 4'hF && B == 4'hF && Cin == 1'b1) |-> (S == 4'hF && Cout == 1'b1)
    );

    ///// Temporal consistency for pure combinational logic /////
    // Stable inputs imply stable outputs.
    check_stable_inputs_hold_outputs: assert property (
        @(posedge CLK) ($stable(A) && $stable(B) && $stable(Cin)) |-> ($stable(S) && $stable(Cout))
    );

    // If A and B are stable and Cin rises, the 5-bit sum increments by 1.
    check_cin_rise_increments_sum: assert property (
        @(posedge CLK) ($stable(A) && $stable(B) && $rose(Cin)) |-> ({Cout, S} == ($past({Cout, S}) + 5'd1))
    );

    // If A and B are stable and Cin falls, the 5-bit sum decrements by 1.
    check_cin_fall_decrements_sum: assert property (
        @(posedge CLK) ($stable(A) && $stable(B) && $fell(Cin)) |-> ({Cout, S} == ($past({Cout, S}) - 5'd1))
    );

    // Swapping A and B across cycles with Cin unchanged preserves outputs.
    check_commutativity_over_time: assert property (
        @(posedge CLK) ((A == $past(B)) && (B == $past(A)) && (Cin == $past(Cin))) |-> ({Cout, S} == $past({Cout, S}))
    );
endmodule