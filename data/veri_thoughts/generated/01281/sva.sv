module complement_concat_sva (
    input logic CLK,
    input logic RESETn,
    input logic [15:0] data_in,
    input logic [31:0] comp_concat_out
);
    // Output equals input concatenated with its bitwise complement.
    check_concat_exact: assert property (
        @(posedge CLK) disable iff (!RESETn)
            comp_concat_out == {data_in, ~data_in}
    );

    // Upper 16 bits mirror data_in.
    check_upper_matches_input: assert property (
        @(posedge CLK) disable iff (!RESETn)
            comp_concat_out[31:16] == data_in
    );

    // Lower 16 bits are bitwise complement of data_in.
    check_lower_is_complement: assert property (
        @(posedge CLK) disable iff (!RESETn)
            comp_concat_out[15:0] == ~data_in
    );

    // Upper half is bitwise complement of lower half.
    check_upper_complements_lower: assert property (
        @(posedge CLK) disable iff (!RESETn)
            comp_concat_out[31:16] == ~comp_concat_out[15:0]
    );

    // Lower half XOR input is all ones.
    check_lower_xor_all_ones: assert property (
        @(posedge CLK) disable iff (!RESETn)
            (comp_concat_out[15:0] ^ data_in) == 16'hFFFF
    );

    // Pairwise OR across halves is all ones.
    check_pairwise_or_ones: assert property (
        @(posedge CLK) disable iff (!RESETn)
            (comp_concat_out[31:16] | comp_concat_out[15:0]) == 16'hFFFF
    );

    // Pairwise AND across halves is all zeros.
    check_pairwise_and_zeros: assert property (
        @(posedge CLK) disable iff (!RESETn)
            (comp_concat_out[31:16] & comp_concat_out[15:0]) == 16'h0000
    );

    // No X/Z on output when input has no X/Z.
    check_no_unknown_when_input_known: assert property (
        @(posedge CLK) disable iff (!RESETn)
            (!$isunknown(data_in)) |-> (!$isunknown(comp_concat_out))
    );

    // If input is stable across cycles, output is stable across cycles.
    check_stability_with_input: assert property (
        @(posedge CLK) disable iff (!RESETn)
            ($past(RESETn) && (data_in == $past(data_in))) |-> (comp_concat_out == $past(comp_concat_out))
    );

    // Upper half toggle mask matches input toggle mask.
    check_upper_toggle_mask: assert property (
        @(posedge CLK) disable iff (!RESETn)
            $past(RESETn) |-> ((comp_concat_out[31:16] ^ $past(comp_concat_out[31:16])) == (data_in ^ $past(data_in)))
    );

    // Lower half toggle mask matches input toggle mask.
    check_lower_toggle_mask: assert property (
        @(posedge CLK) disable iff (!RESETn)
            $past(RESETn) |-> ((comp_concat_out[15:0] ^ $past(comp_concat_out[15:0])) == (data_in ^ $past(data_in)))
    );
endmodule