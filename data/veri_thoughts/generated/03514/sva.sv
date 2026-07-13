module top_module_sva (
    input  logic        clk,
    input  logic [15:0] A,
    input  logic [15:0] B,
    input  logic [3:0]  shift_amt,
    input  logic        less_than,
    input  logic        equal_to,
    input  logic        greater_than,
    input  logic [15:0] shifted_A,
    input  logic [15:0] shifted_B,
    input  logic [15:0] final_output
);

    // less_than reflects the unsigned A < B comparison.
    check_less_than_definition: assert property (
        @(posedge clk) less_than == (A < B)
    );

    // equal_to reflects the A == B comparison.
    check_equal_to_definition: assert property (
        @(posedge clk) equal_to == (A == B)
    );

    // greater_than reflects the unsigned A > B comparison.
    check_greater_than_definition: assert property (
        @(posedge clk) greater_than == (A > B)
    );

    // Exactly one comparator result is asserted each cycle.
    check_comparator_onehot: assert property (
        @(posedge clk) $onehot({less_than, equal_to, greater_than})
    );

    // shifted_A is A logically shifted left by shift_amt.
    check_shifted_a_definition: assert property (
        @(posedge clk) shifted_A == (A << shift_amt)
    );

    // shifted_B is B logically shifted left by shift_amt.
    check_shifted_b_definition: assert property (
        @(posedge clk) shifted_B == (B << shift_amt)
    );

    // In the less-than case, final_output is shifted_A minus shifted_B.
    check_final_output_less_case: assert property (
        @(posedge clk) less_than |-> (final_output == (shifted_A - shifted_B))
    );

    // In the equality case, final_output passes through shifted_A.
    check_final_output_equal_case: assert property (
        @(posedge clk) equal_to |-> (final_output == shifted_A)
    );

    // In the greater-than case, final_output is shifted_A plus shifted_B.
    check_final_output_greater_case: assert property (
        @(posedge clk) greater_than |-> (final_output == (shifted_A + shifted_B))
    );

    // final_output matches the full top-level combinational definition.
    check_final_output_full_definition: assert property (
        @(posedge clk)
        final_output ==
            ((A < B)  ? ((A << shift_amt) - (B << shift_amt)) :
             ((A == B) ?  (A << shift_amt) :
             ((A > B)  ? ((A << shift_amt) + (B << shift_amt)) : 16'b0)))
    );

endmodule