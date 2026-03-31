module and_with_en_sva (
    input logic clk,
    input logic in1,
    input logic in2,
    input logic en,
    input logic out,
    input logic out_valid
);

    // out_valid is a direct copy of en.
    check_out_valid_matches_en: assert property (
        @(posedge clk) out_valid == en
    );

    // out is the AND of in1, in2, and en.
    check_out_matches_and_function: assert property (
        @(posedge clk) out == (in1 & in2 & en)
    );

    // When en is low, out must be low.
    check_en_low_forces_out_low: assert property (
        @(posedge clk) !en |-> !out
    );

    // When en is high, out equals the AND of in1 and in2.
    check_en_high_passes_and: assert property (
        @(posedge clk) en |-> (out == (in1 & in2))
    );

    // A high out requires en and both inputs high.
    check_out_high_requires_en_and_inputs: assert property (
        @(posedge clk) out |-> (en && in1 && in2)
    );

    // With en high and both inputs high, out must be high.
    check_en_and_inputs_high_drive_out_high: assert property (
        @(posedge clk) (en && in1 && in2) |-> out
    );

endmodule