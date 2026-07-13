module consecutive_zeros_counter_sva (
    input logic clk,
    input logic [15:0] in,
    input logic [3:0] out,
    input logic [3:0] stage1_out,
    input logic [15:0] stage2_out,
    input logic [3:0] stage3_out
);

    function automatic [3:0] expected_stage3_from_in(input logic [15:0] din);
        expected_stage3_from_in = 4'd1
                                + {3'b0, (din[11:8] == 4'b0000)}
                                + {3'b0, (din[7:4]  == 4'b0000)}
                                + {3'b0, (din[3:0]  == 4'b0000)};
    endfunction

    function automatic [3:0] zero_nibble_count(input logic [15:0] din);
        zero_nibble_count = {3'b0, (din[15:12] == 4'b0000)}
                          + {3'b0, (din[11:8]  == 4'b0000)}
                          + {3'b0, (din[7:4]   == 4'b0000)}
                          + {3'b0, (din[3:0]   == 4'b0000)};
    endfunction

    // Stage 1 copies the upper input nibble.
    check_stage1_upper_nibble: assert property (
        @(posedge clk) stage1_out == in[15:12]
    );

    // Stage 2 shifts the lower three nibbles up and pads the low nibble with zero.
    check_stage2_mapping: assert property (
        @(posedge clk) stage2_out == {in[11:8], in[7:4], in[3:0], 4'b0000}
    );

    // Stage 3 counts the zero-valued nibbles in stage2_out.
    check_stage3_zero_count: assert property (
        @(posedge clk) stage3_out == zero_nibble_count(stage2_out)
    );

    // Stage 3 matches the zero-count implied directly by the input.
    check_stage3_from_input: assert property (
        @(posedge clk) stage3_out == expected_stage3_from_in(in)
    );

    // Stage 3 is always between one and four.
    check_stage3_range: assert property (
        @(posedge clk) (stage3_out >= 4'd1) && (stage3_out <= 4'd4)
    );

    // The output is the sum of stage1_out and stage3_out.
    check_out_stage_sum: assert property (
        @(posedge clk) out == (stage1_out + stage3_out)
    );

    // The output matches the full input-derived expression.
    check_out_end_to_end: assert property (
        @(posedge clk) out == (in[15:12] + expected_stage3_from_in(in))
    );

    // If no lower input nibble is zero, the count is one.
    check_stage3_only_padded_zero: assert property (
        @(posedge clk)
        (in[11:8] != 4'b0000 && in[7:4] != 4'b0000 && in[3:0] != 4'b0000) |-> (stage3_out == 4'd1)
    );

    // If all lower input nibbles are zero, the count is four.
    check_stage3_all_zero_nibbles: assert property (
        @(posedge clk)
        (in[11:8] == 4'b0000 && in[7:4] == 4'b0000 && in[3:0] == 4'b0000) |-> (stage3_out == 4'd4)
    );

endmodule