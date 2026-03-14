module top_module_sva (
    input logic CLK,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic enable,
    input logic [3:0] q
);
    ///// Combinational selection rules /////
    // When enable is LOW, q equals B.
    check_q_equals_B_when_enable_low: assert property (
        @(posedge CLK) disable iff (1'b0) (!enable) |-> (q == B)
    );

    // When enable is HIGH and A >= B, q equals A.
    check_q_equals_A_when_enable_high_and_A_ge_B: assert property (
        @(posedge CLK) disable iff (1'b0) (enable && (A >= B)) |-> (q == A)
    );

    // When enable is HIGH and A < B, q equals B.
    check_q_equals_B_when_enable_high_and_A_lt_B: assert property (
        @(posedge CLK) disable iff (1'b0) (enable && (A < B)) |-> (q == B)
    );

    // If A < B, q must be B regardless of enable.
    check_q_equals_B_when_A_lt_B: assert property (
        @(posedge CLK) disable iff (1'b0) (A < B) |-> (q == B)
    );

    // q is always either A or B.
    check_q_is_A_or_B: assert property (
        @(posedge CLK) disable iff (1'b0) ((q == A) || (q == B))
    );

    // Functional equivalence: q == (enable && (A >= B) ? A : B).
    check_mux_equivalence: assert property (
        @(posedge CLK) disable iff (1'b0) (q == ((enable && (A >= B)) ? A : B))
    );

    // When A == B and enable is HIGH, q equals A.
    check_equal_inputs_with_enable: assert property (
        @(posedge CLK) disable iff (1'b0) (enable && (A == B)) |-> (q == A)
    );

    // When A == B and enable is LOW, q equals B.
    check_equal_inputs_without_enable: assert property (
        @(posedge CLK) disable iff (1'b0) (!enable && (A == B)) |-> (q == B)
    );
endmodule