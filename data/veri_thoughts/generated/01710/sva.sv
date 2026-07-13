module combinational_logic_sva (
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1_N
);
    ///// Combinational function /////
    // Y must equal (A1 & !A2) | !B1_N.
    check_function_equivalence: assert property (
        @(posedge $global_clock) Y == ((A1 && !A2) || !B1_N)
    );

    ///// Dominance and reduction rules /////
    // B1_N LOW forces Y HIGH.
    check_B1N_low_forces_Y_high: assert property (
        @(posedge $global_clock) (B1_N == 1'b0) |-> (Y == 1'b1)
    );

    // When B1_N is HIGH, Y reduces to (A1 & !A2).
    check_B1N_high_reduction: assert property (
        @(posedge $global_clock) (B1_N == 1'b1) |-> (Y == (A1 && !A2))
    );

    ///// Useful minterm implications /////
    // If A1=1 and A2=0, Y must be HIGH.
    check_A1_1_A2_0_forces_Y_high: assert property (
        @(posedge $global_clock) (A1 == 1'b1 && A2 == 1'b0) |-> (Y == 1'b1)
    );

    // If B1_N=1 and A1=0, Y must be LOW.
    check_B1N_high_A1_0_forces_Y_low: assert property (
        @(posedge $global_clock) (B1_N == 1'b1 && A1 == 1'b0) |-> (Y == 1'b0)
    );

    // If B1_N=1 and A2=1, Y must be LOW.
    check_B1N_high_A2_1_forces_Y_low: assert property (
        @(posedge $global_clock) (B1_N == 1'b1 && A2 == 1'b1) |-> (Y == 1'b0)
    );

    ///// Output implication checks /////
    // Y LOW implies B1_N is HIGH and either A1=0 or A2=1.
    check_Y_low_implies_inputs: assert property (
        @(posedge $global_clock) (Y == 1'b0) |-> (B1_N == 1'b1) && ((A1 == 1'b0) || (A2 == 1'b1))
    );

    // Y HIGH implies B1_N is LOW or (A1=1 and A2=0).
    check_Y_high_implies_inputs: assert property (
        @(posedge $global_clock) (Y == 1'b1) |-> ((B1_N == 1'b0) || (A1 == 1'b1 && A2 == 1'b0))
    );
endmodule