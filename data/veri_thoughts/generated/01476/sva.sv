module four_bit_adder_sva (
    input logic CLK,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic Cin,
    input logic [3:0] S,
    input logic Cout
);
    // No clock/reset in DUT; purely combinational NAND network. Assertions sample at posedge CLK; no reset gating.

    ///// Functional equivalence to RTL equations /////
    // S[0] equals ~(~(A0 & B0) & Cin).
    check_s0_matches_logic: assert property (
        @(posedge CLK) disable iff (1'b0)
        S[0] === ~( (~(A[0] & B[0])) & Cin )
    );

    // S[1] equals ~(~(A1 & B1) & ~(B0 & Cin)).
    check_s1_matches_logic: assert property (
        @(posedge CLK) disable iff (1'b0)
        S[1] === ~( (~(A[1] & B[1])) & ~(B[0] & Cin) )
    );

    // S[2] equals ~(~(A2 & B2) & ~(B1 & ~(B0 & Cin))).
    check_s2_matches_logic: assert property (
        @(posedge CLK) disable iff (1'b0)
        S[2] === ~( (~(A[2] & B[2])) & ~(B[1] & ~(B[0] & Cin)) )
    );

    // S[3] equals ~(~(A3 & B3) & ~(B2 & ~(B1 & ~(B0 & Cin)))).
    check_s3_matches_logic: assert property (
        @(posedge CLK) disable iff (1'b0)
        S[3] === ~( (~(A[3] & B[3])) & ~(B[2] & ~(B[1] & ~(B[0] & Cin))) )
    );

    // Cout equals ~(B3 & ~(B2 & ~(B1 & ~(B0 & Cin)))).
    check_cout_matches_logic: assert property (
        @(posedge CLK) disable iff (1'b0)
        Cout === ~( B[3] & ~(B[2] & ~(B[1] & ~(B[0] & Cin))) )
    );

    ///// Combinational stability /////
    // If inputs are stable, outputs must be stable.
    check_outputs_stable_when_inputs_stable: assert property (
        @(posedge CLK) disable iff (1'b0)
        ($stable(A) && $stable(B) && $stable(Cin)) |-> ($stable(S) && $stable(Cout))
    );

    // Outputs can change only if at least one input changed.
    check_outputs_change_requires_input_change: assert property (
        @(posedge CLK) disable iff (1'b0)
        ($changed(S) || $changed(Cout)) |-> ($changed(A) || $changed(B) || $changed(Cin))
    );

    ///// Independence from irrelevant inputs /////
    // S[0] is independent of A[3:1] and B[3:1] when A[0],B[0],Cin are stable.
    check_s0_independent_of_upper_inputs: assert property (
        @(posedge CLK) disable iff (1'b0)
        ($stable(A[0]) && $stable(B[0]) && $stable(Cin) && $changed({A[3:1],B[3:1]})) |-> $stable(S[0])
    );

    // S[1] is independent of A[3:2],A[0],B[3:2] when A[1],B[1],B[0],Cin are stable.
    check_s1_independent_of_irrelevant_inputs: assert property (
        @(posedge CLK) disable iff (1'b0)
        ($stable(A[1]) && $stable(B[1]) && $stable(B[0]) && $stable(Cin) && $changed({A[3:2],A[0],B[3:2]})) |-> $stable(S[1])
    );

    // S[2] is independent of A[3],A[1:0],B[3] when A[2],B[2],B[1],B[0],Cin are stable.
    check_s2_independent_of_irrelevant_inputs: assert property (
        @(posedge CLK) disable iff (1'b0)
        ($stable(A[2]) && $stable(B[2]) && $stable(B[1]) && $stable(B[0]) && $stable(Cin) && $changed({A[3],A[1:0],B[3]})) |-> $stable(S[2])
    );

    // S[3] is independent of A[2:0] when A[3],B[3:0],Cin are stable.
    check_s3_independent_of_lower_A_bits: assert property (
        @(posedge CLK) disable iff (1'b0)
        ($stable(A[3]) && $stable(B) && $stable(Cin) && $changed(A[2:0])) |-> $stable(S[3])
    );

    // Cout is independent of A when B and Cin are stable.
    check_cout_independent_of_A: assert property (
        @(posedge CLK) disable iff (1'b0)
        ($stable(B) && $stable(Cin) && $changed(A)) |-> $stable(Cout)
    );

    ///// Simple corner case implied by the NAND structure /////
    // When B==0, S[3:1]==0, S[0]==~Cin, Cout==1.
    check_behavior_when_B_is_zero: assert property (
        @(posedge CLK) disable iff (1'b0)
        (B === 4'b0000) |-> ((S[3:1] === 3'b000) && (S[0] === ~Cin) && (Cout === 1'b1))
    );

endmodule