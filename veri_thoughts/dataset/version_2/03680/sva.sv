module five_input_gate_sva (
    input logic clk,
    input logic in1,
    input logic in2,
    input logic in3,
    input logic in4,
    input logic in5,
    input logic out
);

    // Output matches the implemented OR-of-ANDs function.
    check_out_matches_boolean_function: assert property (
        @(posedge clk) out == ((in1 & in2) | (in3 & in4) | in5)
    );

    // Fifth input directly forces the output high.
    check_in5_forces_out_high: assert property (
        @(posedge clk) in5 |-> out
    );

    // First input pair forces the output high when both are high.
    check_first_pair_forces_out_high: assert property (
        @(posedge clk) (in1 & in2) |-> out
    );

    // Second input pair forces the output high when both are high.
    check_second_pair_forces_out_high: assert property (
        @(posedge clk) (in3 & in4) |-> out
    );

    // A high output must come from at least one implemented source term.
    check_out_high_has_active_source: assert property (
        @(posedge clk) out |-> ((in1 & in2) | (in3 & in4) | in5)
    );

    // Output stays low when all three OR terms are low.
    check_out_low_when_all_terms_low: assert property (
        @(posedge clk) ((!(in1 & in2)) && (!(in3 & in4)) && (!in5)) |-> (!out)
    );

endmodule