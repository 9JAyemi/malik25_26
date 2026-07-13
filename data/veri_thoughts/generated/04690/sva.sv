module halfword_separator_sva (
    input logic        clk,
    input logic [15:0] in,
    input logic        select_upper,
    input logic [7:0]  out_hi,
    input logic [7:0]  out_lo
);

    // out_hi always equals the upper input byte.
    check_out_hi_matches_upper_byte: assert property (
        @(posedge clk) out_hi == in[15:8]
    );

    // out_lo selects the lower or upper byte based on select_upper.
    check_out_lo_matches_selected_byte: assert property (
        @(posedge clk) out_lo == (select_upper ? in[7:0] : in[15:8])
    );

    // With select_upper high, the outputs reproduce the input halfword.
    check_passthrough_when_select_upper: assert property (
        @(posedge clk) select_upper |-> ({out_hi, out_lo} == in)
    );

    // With select_upper low, both outputs equal the upper input byte.
    check_upper_byte_duplicated_when_select_lower: assert property (
        @(posedge clk) !select_upper |-> ({out_hi, out_lo} == {in[15:8], in[15:8]})
    );

    // With select_upper low, the two outputs must match.
    check_outputs_match_when_select_lower: assert property (
        @(posedge clk) !select_upper |-> (out_hi == out_lo)
    );

endmodule