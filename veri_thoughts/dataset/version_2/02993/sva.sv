module and_module_sva (
    input  logic        CLK,            // sampling clock for SVA
    input  logic [7:0]  A,
    input  logic [7:0]  B,
    input  logic        output_signal,
    input  logic [7:0]  and_result      // internal wire from RTL
);
    // Internal and_result equals bitwise A & B.
    check_and_result_bitwise_and: assert property (
        @(posedge CLK) disable iff (1'b0) and_result == (A & B)
    );

    // Output equals AND-reduction of internal and_result.
    check_output_equals_reduction_of_internal: assert property (
        @(posedge CLK) disable iff (1'b0) output_signal == (&and_result)
    );

    // Output equals AND-reduction across bitwise pairs A & B.
    check_output_equals_and_of_pairs: assert property (
        @(posedge CLK) disable iff (1'b0) output_signal == &(A & B)
    );

    // If output is 1, then all bits of A and B are 1.
    check_output_one_implies_all_ones: assert property (
        @(posedge CLK) disable iff (1'b0) output_signal |-> ((&A) && (&B))
    );

    // If all bits of A and B are 1, then output is 1.
    check_all_ones_implies_output_one: assert property (
        @(posedge CLK) disable iff (1'b0) ((&A) && (&B)) |-> (output_signal == 1'b1)
    );

    // If any bit of A is 0, output must be 0.
    check_any_zero_in_A_forces_zero: assert property (
        @(posedge CLK) disable iff (1'b0) (~&A) |-> (output_signal == 1'b0)
    );

    // If any bit of B is 0, output must be 0.
    check_any_zero_in_B_forces_zero: assert property (
        @(posedge CLK) disable iff (1'b0) (~&B) |-> (output_signal == 1'b0)
    );
endmodule