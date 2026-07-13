module and_with_en_sva (
    input logic in1,
    input logic in2,
    input logic en,
    input logic out,
    input logic out_valid
);
    // Ensure that out is only valid when en is high
    valid_when_en: assert property (
        @(posedge clk) disable iff (!resetn) out_valid |-> en
    );

    // Ensure that out is the result of in1 and in2 when en is high
    correct_output: assert property (
        @(posedge clk) disable iff (!resetn) (en == 1'b1) |-> (out == (in1 & in2))
    );

    // Ensure that out_valid is high when en is high
    out_valid_when_en: assert property (
        @(posedge clk) disable iff (!resetn) en |-> out_valid
    );

    // Ensure that out_valid is low when en is low
    out_valid_when_en_low: assert property (
        @(posedge clk) disable iff (!resetn) !en |-> !out_valid
    );

    // Ensure that out is low when en is low
    out_when_en_low: assert property (
        @(posedge clk) disable iff (!resetn) !en |-> !out
    );

    // Ensure that out is low when in1 is low and en is high
    out_when_in1_low: assert property (
        @(posedge clk) disable iff (!resetn) (en == 1'b1) & !in1 |-> !out
    );

    // Ensure that out is low when in2 is low and en is high
    out_when_in2_low: assert property (
        @(posedge clk) disable iff (!resetn) (en == 1'b1) & !in2 |-> !out
    );

    // Ensure that out is high when in1 and in2 are high and en is high
    out_when_in1_in2_high: assert property (
        @(posedge clk) disable iff (!resetn) (en == 1'b1) & in1 & in2 |-> out
    );

    // Ensure that out is low when in1 is high and in2 is low and en is high
    out_when_in1_high_in2_low: assert property (
        @(posedge clk) disable iff (!resetn) (en == 1'b1) & in1 & !in2 |-> !out
    );

    // Ensure that out is low when in1 is low and in2 is high and en is high
    out_when_in1_low_in2_high: assert property (
        @(posedge clk) disable iff (!resetn) (en == 1'b1) & !in1 & in2 |-> !out
    );

endmodule