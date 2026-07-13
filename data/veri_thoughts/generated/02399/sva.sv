module full_adder_sva (
    input  logic CLK,
    input  logic RST,   // active-high reset used only to gate assertions
    input  logic A,
    input  logic B,
    input  logic CIN,
    input  logic COUT,
    input  logic SUM
);
    // SUM equals XOR of inputs.
    check_sum_xor: assert property (
        @(posedge CLK) disable iff (RST) SUM == (A ^ B ^ CIN)
    );

    // COUT equals majority function of inputs.
    check_carry_majority: assert property (
        @(posedge CLK) disable iff (RST) COUT == ((A & B) | (B & CIN) | (A & CIN))
    );

    // {COUT,SUM} equals the 2-bit arithmetic sum of A+B+CIN.
    check_add_equivalence: assert property (
        @(posedge CLK) disable iff (RST) {COUT, SUM} == ({1'b0,A} + {1'b0,B} + {1'b0,CIN})
    );

    // When A equals B, SUM mirrors CIN.
    check_sum_when_inputs_equal: assert property (
        @(posedge CLK) disable iff (RST) (A == B) |-> (SUM == CIN)
    );

    // All inputs zero produce outputs 00.
    check_zero_input_case: assert property (
        @(posedge CLK) disable iff (RST) (!A && !B && !CIN) |-> ({COUT, SUM} == 2'b00)
    );

    // Exactly one input high produces outputs 01.
    check_onehot_case: assert property (
        @(posedge CLK) disable iff (RST) $onehot({A,B,CIN}) |-> ({COUT, SUM} == 2'b01)
    );

    // Exactly two inputs high produce outputs 10.
    check_twohot_case: assert property (
        @(posedge CLK) disable iff (RST) ($countones({A,B,CIN}) == 2) |-> ({COUT, SUM} == 2'b10)
    );

    // All three inputs high produce outputs 11.
    check_all_ones_case: assert property (
        @(posedge CLK) disable iff (RST) (A && B && CIN) |-> ({COUT, SUM} == 2'b11)
    );

    // Carry must be 1 when at least two inputs are 1.
    check_carry_ge_two_ones: assert property (
        @(posedge CLK) disable iff (RST) ($countones({A,B,CIN}) >= 2) |-> (COUT == 1'b1)
    );

    // Carry must be 0 when zero or one input is 1.
    check_carry_le_one_one: assert property (
        @(posedge CLK) disable iff (RST) ($countones({A,B,CIN}) <= 1) |-> (COUT == 1'b0)
    );
endmodule