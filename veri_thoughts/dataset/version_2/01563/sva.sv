module comparator_4bit_sva (
    input logic CLK,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic EQ,
    input logic GT
);
    // EQ must reflect (A == B).
    check_eq_definition: assert property (
        @(posedge CLK) (EQ === (A == B))
    );

    // GT must reflect (A > B).
    check_gt_definition: assert property (
        @(posedge CLK) (GT === (A > B))
    );

    // EQ and GT cannot be high at the same time.
    check_outputs_mutex: assert property (
        @(posedge CLK) !((EQ === 1'b1) && (GT === 1'b1))
    );

    // When A == B, outputs must be EQ=1 and GT=0.
    check_equal_case_outputs: assert property (
        @(posedge CLK) (A == B) |-> ((EQ === 1'b1) && (GT === 1'b0))
    );

    // When A > B, outputs must be GT=1 and EQ=0.
    check_greater_case_outputs: assert property (
        @(posedge CLK) (A > B) |-> ((GT === 1'b1) && (EQ === 1'b0))
    );

    // When A < B, outputs must be EQ=0 and GT=0.
    check_less_case_outputs: assert property (
        @(posedge CLK) (A < B) |-> ((EQ === 1'b0) && (GT === 1'b0))
    );

    // If EQ is asserted, inputs must be equal.
    check_eq_high_implies_inputs_equal: assert property (
        @(posedge CLK) (EQ === 1'b1) |-> (A == B)
    );

    // If GT is asserted, A must be greater than B.
    check_gt_high_implies_a_greater: assert property (
        @(posedge CLK) (GT === 1'b1) |-> (A > B)
    );
endmodule