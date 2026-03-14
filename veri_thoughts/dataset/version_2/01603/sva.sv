module byte_reorder_sva (
    input logic clk,
    input logic [31:0] in,
    input logic [31:0] out
);
    // Clock: clk; no reset present. Sequential pipeline with 1-cycle byte-reversal latency.

    // Out equals previous cycle's input with bytes reversed.
    check_out_prev_in_reversed: assert property (
        @(posedge clk) out == { $past(in[7:0]), $past(in[15:8]), $past(in[23:16]), $past(in[31:24]) }
    );

    // MSB byte of out equals LSB byte of previous input.
    check_out31_24_eq_past_in7_0: assert property (
        @(posedge clk) out[31:24] == $past(in[7:0])
    );

    // Second MSB byte of out equals previous input[15:8].
    check_out23_16_eq_past_in15_8: assert property (
        @(posedge clk) out[23:16] == $past(in[15:8])
    );

    // Second LSB byte of out equals previous input[23:16].
    check_out15_8_eq_past_in23_16: assert property (
        @(posedge clk) out[15:8] == $past(in[23:16])
    );

    // LSB byte of out equals MSB byte of previous input.
    check_out7_0_eq_past_in31_24: assert property (
        @(posedge clk) out[7:0] == $past(in[31:24])
    );

    // Change in input byte0 causes change in out byte3 next cycle.
    check_in_byte0_change_causes_out_byte3_change_next: assert property (
        @(posedge clk) $changed(in[7:0]) |-> ##1 $changed(out[31:24])
    );

    // Change in input byte1 causes change in out byte2 next cycle.
    check_in_byte1_change_causes_out_byte2_change_next: assert property (
        @(posedge clk) $changed(in[15:8]) |-> ##1 $changed(out[23:16])
    );

    // Change in input byte2 causes change in out byte1 next cycle.
    check_in_byte2_change_causes_out_byte1_change_next: assert property (
        @(posedge clk) $changed(in[23:16]) |-> ##1 $changed(out[15:8])
    );

    // Change in input byte3 causes change in out byte0 next cycle.
    check_in_byte3_change_causes_out_byte0_change_next: assert property (
        @(posedge clk) $changed(in[31:24]) |-> ##1 $changed(out[7:0])
    );

    // If input is stable this cycle, output is stable next cycle.
    check_stable_in_implies_stable_out_next: assert property (
        @(posedge clk) $stable(in) |-> ##1 $stable(out)
    );
endmodule