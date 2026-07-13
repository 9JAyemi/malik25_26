module max_8bit_sva (
    input logic clk,           // sampling clock for assertions
    input logic [7:0] A,
    input logic [7:0] B,
    input logic [7:0] max_val
);
    // Analysis: no clock/reset in DUT; pure combinational; max_val = (A > B) ? A : B.

    // Functional equivalence to ternary form.
    check_functional_spec: assert property (
        @(posedge clk) max_val == ((A > B) ? A : B)
    );

    // If A is strictly greater than B, output must be A.
    check_select_A_when_gt: assert property (
        @(posedge clk) (A > B) |-> (max_val == A)
    );

    // If A is less than or equal to B, output must be B.
    check_select_B_when_le: assert property (
        @(posedge clk) (A <= B) |-> (max_val == B)
    );

    // On ties, output equals both inputs (they are equal).
    check_tie_outputs_equal: assert property (
        @(posedge clk) (A == B) |-> ((max_val == A) && (max_val == B))
    );

    // Output must equal one of the inputs.
    check_output_is_input_value: assert property (
        @(posedge clk) (max_val == A) || (max_val == B)
    );

    // Output is not less than A.
    check_output_ge_A: assert property (
        @(posedge clk) max_val >= A
    );

    // Output is not less than B.
    check_output_ge_B: assert property (
        @(posedge clk) max_val >= B
    );

    // If output equals A, then A is at least B.
    check_output_eq_A_implies_A_ge_B: assert property (
        @(posedge clk) (max_val == A) |-> (A >= B)
    );

    // If output equals B, then B is at least A.
    check_output_eq_B_implies_B_ge_A: assert property (
        @(posedge clk) (max_val == B) |-> (B >= A)
    );

    // If A is strictly less than B, output cannot be A.
    check_no_A_when_A_lt_B: assert property (
        @(posedge clk) (A < B) |-> (max_val != A)
    );
endmodule