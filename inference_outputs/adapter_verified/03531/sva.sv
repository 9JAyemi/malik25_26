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

// When en is low, out must be low.
    check_out_low_when_en_low: assert property (
        @(posedge clk) !en |-> !out
    );

// When en is high, out equals in1 AND in2.
    check_out_equals_and_when_en_high: assert property (
        @(posedge clk) en |-> (out == (in1 & in2))
    );

// A high out requires both inputs high and en high.
    check_out_high_requires_en_and_inputs: assert property (
        @(posedge clk) out |-> (en && in1 && in2)
    );

// A high en with both inputs high drives out high.
    check_out_high_when_en_and_inputs_high: assert property (
        @(posedge clk) (en && in1 && in2) |-> out
    );

endmodule
