module half_adder_sva (
    input logic CLK,   // Assertion sampling clock (DUT is combinational)
    input logic A,
    input logic B,
    input logic SUM,
    input logic COUT
);
    // Analysis: no reset in RTL; pure combinational; SUM=A^B, COUT=A&B.

    // SUM equals A XOR B.
    check_sum_def: assert property (
        @(posedge CLK) SUM == (A ^ B)
    );

    // COUT equals A AND B.
    check_cout_def: assert property (
        @(posedge CLK) COUT == (A & B)
    );

    // SUM and COUT are never both 1.
    check_sum_cout_mutex: assert property (
        @(posedge CLK) !(SUM & COUT)
    );

    // COUT high implies both inputs are high.
    check_cout_implies_both_one: assert property (
        @(posedge CLK) COUT |-> (A && B)
    );

    // Both inputs high implies COUT is high.
    check_both_one_implies_cout: assert property (
        @(posedge CLK) (A && B) |-> COUT
    );

    // Exactly one input high implies SUM=1 and COUT=0.
    check_one_hot_inputs_outputs: assert property (
        @(posedge CLK) (A ^ B) |-> (SUM == 1'b1) && (COUT == 1'b0)
    );

    // Inputs equal implies SUM=0.
    check_inputs_equal_sum_zero: assert property (
        @(posedge CLK) (A == B) |-> (SUM == 1'b0)
    );

    // Inputs equal implies COUT equals the input value.
    check_inputs_equal_cout_equals_input: assert property (
        @(posedge CLK) (A == B) |-> (COUT == A)
    );

endmodule