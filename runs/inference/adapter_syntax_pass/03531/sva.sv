module and_with_en_sva (
    input logic clk,
    input logic in1,
    input logic in2,
    input logic en,
    input logic out,
    input logic out_valid
);

    // out_valid is always equal to en.
    check_out_valid_matches_en: assert property (
        @(posedge clk) out_valid == en
    );

    // out is high only when en is high and both inputs are high.
    check_out_matches_enabled_and: assert property (
        @(posedge clk) out == (en && in1 && in2)
    );

    // out is low whenever en is low.
    check_out_low_when_en_low: assert property (
        @(posedge clk) !en |-> !out
    );

    // out is low whenever in1 is low.
    check_out_low_when_in1_low: assert property (
        @(posedge clk) !in1 |-> !out
    );

    // out is low whenever in2 is low.
    check_out_low_when_in2_low: assert property (
        @(posedge clk) !in2 |-> !out
    );

    // out is high when en and both inputs are high.
    check_out_high_when_all_high: assert property (
        @(posedge clk) (en && in1 && in2) |-> out
    );

endmodule