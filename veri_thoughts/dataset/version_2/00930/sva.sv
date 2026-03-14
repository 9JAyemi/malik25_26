module m_4bit_comparator_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic EQ
);
    // EQ must reflect whether A equals B.
    check_eq_definition: assert property (
        @(posedge clk) (EQ == (A == B))
    );

    // When EQ is HIGH, A must equal B.
    check_eq_high_implies_equal: assert property (
        @(posedge clk) EQ |-> (A == B)
    );

    // When EQ is LOW, A must not equal B.
    check_eq_low_implies_unequal: assert property (
        @(posedge clk) !EQ |-> (A != B)
    );

    // If inputs are stable, EQ must remain stable.
    check_stable_inputs_imply_stable_eq: assert property (
        @(posedge clk) $stable(A) && $stable(B) |-> $stable(EQ)
    );

    // EQ can only change if at least one input changes.
    check_eq_change_requires_input_change: assert property (
        @(posedge clk) $changed(EQ) |-> ($changed(A) || $changed(B))
    );
endmodule