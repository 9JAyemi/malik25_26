module top_module_assertions(
    input logic [15:0] in,
    input logic [7:0]  out_hi,
    input logic [7:0]  out_lo,
    input logic        clk,
    input logic [15:0] stage1_out,
    input logic [7:0]  stage2_out_hi,
    input logic [7:0]  stage2_out_lo,
    input logic [15:0] shifted_data
);

    // shifted_data is the input shifted right by 8 bits.
    check_shifted_data_definition: assert property (
        @(posedge clk) (shifted_data == (in >> 8))
    );

    // stage1_out captures shifted_data on the previous clock.
    check_stage1_captures_shifted_data: assert property (
        @(posedge clk) (!$initstate) |-> (stage1_out == $past(shifted_data))
    );

    // stage1_out low byte comes from the previous input high byte.
    check_stage1_lower_byte_mapping: assert property (
        @(posedge clk) (!$initstate) |-> (stage1_out[7:0] == $past(in[15:8]))
    );

    // stage1_out high byte is zero after the right shift by 8.
    check_stage1_upper_byte_zero: assert property (
        @(posedge clk) (!$initstate) |-> (stage1_out[15:8] == 8'h00)
    );

    // stage2_out_hi captures the previous stage1_out high byte.
    check_stage2_hi_captures_stage1_upper: assert property (
        @(posedge clk) (!$initstate) |-> (stage2_out_hi == $past(stage1_out[15:8]))
    );

    // stage2_out_lo captures the previous input low byte.
    check_stage2_lo_captures_input_lower: assert property (
        @(posedge clk) (!$initstate) |-> (stage2_out_lo == $past(in[7:0]))
    );

    // out_hi is directly driven by stage2_out_hi.
    check_out_hi_matches_stage2: assert property (
        @(posedge clk) (out_hi == stage2_out_hi)
    );

    // out_lo is directly driven by stage2_out_lo.
    check_out_lo_matches_stage2: assert property (
        @(posedge clk) (out_lo == stage2_out_lo)
    );

    // out_lo reflects the previous input low byte.
    check_out_lo_one_cycle_latency: assert property (
        @(posedge clk) (!$initstate) |-> (out_lo == $past(in[7:0]))
    );

    // A zero high byte in stage1_out reaches out_hi on the next clock.
    check_zero_high_byte_propagates_to_output: assert property (
        @(posedge clk) (stage1_out[15:8] == 8'h00) |=> (out_hi == 8'h00)
    );

endmodule