module four_or_gate_sva (
    input logic clk,
    input logic in1,
    input logic in2,
    input logic in3,
    input logic in4,
    input logic out
);

    // Output must equal the OR of all four inputs.
    check_out_matches_or: assert property (
        @(posedge clk) out == (in1 | in2 | in3 | in4)
    );

    // Any asserted input must make the output high.
    check_any_input_drives_out_high: assert property (
        @(posedge clk) (in1 | in2 | in3 | in4) |-> out
    );

    // A high output must be caused by at least one high input.
    check_out_high_implies_input_high: assert property (
        @(posedge clk) out |-> (in1 | in2 | in3 | in4)
    );

    // All inputs low must make the output low.
    check_all_inputs_low_drives_out_low: assert property (
        @(posedge clk) !(in1 | in2 | in3 | in4) |-> !out
    );

    // A low output implies all inputs are low.
    check_out_low_implies_all_inputs_low: assert property (
        @(posedge clk) !out |-> !(in1 | in2 | in3 | in4)
    );

    // in1 alone being high must force the output high.
    check_in1_drives_out_high: assert property (
        @(posedge clk) in1 |-> out
    );

    // in2 alone being high must force the output high.
    check_in2_drives_out_high: assert property (
        @(posedge clk) in2 |-> out
    );

    // in3 alone being high must force the output high.
    check_in3_drives_out_high: assert property (
        @(posedge clk) in3 |-> out
    );

    // in4 alone being high must force the output high.
    check_in4_drives_out_high: assert property (
        @(posedge clk) in4 |-> out
    );

endmodule