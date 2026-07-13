module full_adder_sva (
    input logic CLK,   // External sampling clock (DUT is combinational, no reset)
    input logic A,
    input logic B,
    input logic CIN,
    input logic SUM,
    input logic COUT
);

    // COUT equals majority of A,B,CIN.
    check_cout_is_majority: assert property (
        @(posedge CLK) COUT == ((A & B) | (A & CIN) | (B & CIN))
    );

    // SUM equals (A^B^CIN) xor majority(A,B,CIN).
    check_sum_equals_xor_with_carry: assert property (
        @(posedge CLK) SUM == ((A ^ B ^ CIN) ^ ((A & B) | (A & CIN) | (B & CIN)))
    );

    // When no carry, SUM equals parity of inputs.
    check_sum_when_cout0: assert property (
        @(posedge CLK) (COUT == 1'b0) |-> (SUM == (A ^ B ^ CIN))
    );

    // When carry, SUM is inverse of parity.
    check_sum_when_cout1: assert property (
        @(posedge CLK) (COUT == 1'b1) |-> (SUM == ~(A ^ B ^ CIN))
    );

    // Exactly one input high -> SUM=1, COUT=0.
    check_onehot_inputs: assert property (
        @(posedge CLK) $onehot({A,B,CIN}) |-> (SUM == 1'b1) && (COUT == 1'b0)
    );

    // All inputs low -> outputs low.
    check_all_zero_case: assert property (
        @(posedge CLK) (~A & ~B & ~CIN) |-> (SUM == 1'b0) && (COUT == 1'b0)
    );

    // All inputs high -> SUM=0, COUT=1.
    check_all_one_case: assert property (
        @(posedge CLK) (A & B & CIN) |-> (SUM == 1'b0) && (COUT == 1'b1)
    );

    // Two ones: A&B=1 and CIN=0 -> SUM=1, COUT=1.
    check_two_ones_AB: assert property (
        @(posedge CLK) (A & B & ~CIN) |-> (SUM == 1'b1) && (COUT == 1'b1)
    );

    // Two ones: A&CIN=1 and B=0 -> SUM=1, COUT=1.
    check_two_ones_AC: assert property (
        @(posedge CLK) (A & CIN & ~B) |-> (SUM == 1'b1) && (COUT == 1'b1)
    );

    // Two ones: B&CIN=1 and A=0 -> SUM=1, COUT=1.
    check_two_ones_BC: assert property (
        @(posedge CLK) (B & CIN & ~A) |-> (SUM == 1'b1) && (COUT == 1'b1)
    );

endmodule