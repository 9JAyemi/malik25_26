module sparc_ifu_par32_sva (
    input logic [31:0] in,
    input logic        out
);

    // out equals XOR reduction of in on any input or output edge.
    check_out_matches_reduction_xor: assert property (
        @(posedge in[0]  or negedge in[0]  or
          posedge in[1]  or negedge in[1]  or
          posedge in[2]  or negedge in[2]  or
          posedge in[3]  or negedge in[3]  or
          posedge in[4]  or negedge in[4]  or
          posedge in[5]  or negedge in[5]  or
          posedge in[6]  or negedge in[6]  or
          posedge in[7]  or negedge in[7]  or
          posedge in[8]  or negedge in[8]  or
          posedge in[9]  or negedge in[9]  or
          posedge in[10] or negedge in[10] or
          posedge in[11] or negedge in[11] or
          posedge in[12] or negedge in[12] or
          posedge in[13] or negedge in[13] or
          posedge in[14] or negedge in[14] or
          posedge in[15] or negedge in[15] or
          posedge in[16] or negedge in[16] or
          posedge in[17] or negedge in[17] or
          posedge in[18] or negedge in[18] or
          posedge in[19] or negedge in[19] or
          posedge in[20] or negedge in[20] or
          posedge in[21] or negedge in[21] or
          posedge in[22] or negedge in[22] or
          posedge in[23] or negedge in[23] or
          posedge in[24] or negedge in[24] or
          posedge in[25] or negedge in[25] or
          posedge in[26] or negedge in[26] or
          posedge in[27] or negedge in[27] or
          posedge in[28] or negedge in[28] or
          posedge in[29] or negedge in[29] or
          posedge in[30] or negedge in[30] or
          posedge in[31] or negedge in[31] or
          posedge out    or negedge out)
        (out == ^in)
    );

    // If inputs are unchanged since last sample, output must be unchanged.
    check_out_stable_when_in_stable: assert property (
        @(posedge in[0]  or negedge in[0]  or
          posedge in[1]  or negedge in[1]  or
          posedge in[2]  or negedge in[2]  or
          posedge in[3]  or negedge in[3]  or
          posedge in[4]  or negedge in[4]  or
          posedge in[5]  or negedge in[5]  or
          posedge in[6]  or negedge in[6]  or
          posedge in[7]  or negedge in[7]  or
          posedge in[8]  or negedge in[8]  or
          posedge in[9]  or negedge in[9]  or
          posedge in[10] or negedge in[10] or
          posedge in[11] or negedge in[11] or
          posedge in[12] or negedge in[12] or
          posedge in[13] or negedge in[13] or
          posedge in[14] or negedge in[14] or
          posedge in[15] or negedge in[15] or
          posedge in[16] or negedge in[16] or
          posedge in[17] or negedge in[17] or
          posedge in[18] or negedge in[18] or
          posedge in[19] or negedge in[19] or
          posedge in[20] or negedge in[20] or
          posedge in[21] or negedge in[21] or
          posedge in[22] or negedge in[22] or
          posedge in[23] or negedge in[23] or
          posedge in[24] or negedge in[24] or
          posedge in[25] or negedge in[25] or
          posedge in[26] or negedge in[26] or
          posedge in[27] or negedge in[27] or
          posedge in[28] or negedge in[28] or
          posedge in[29] or negedge in[29] or
          posedge in[30] or negedge in[30] or
          posedge in[31] or negedge in[31] or
          posedge out    or negedge out)
        (!$initstate && (in == $past(in))) |-> (out == $past(out))
    );

    // If exactly one input bit toggled since last sample, output must toggle.
    check_out_toggles_on_one_input_toggle: assert property (
        @(posedge in[0]  or negedge in[0]  or
          posedge in[1]  or negedge in[1]  or
          posedge in[2]  or negedge in[2]  or
          posedge in[3]  or negedge in[3]  or
          posedge in[4]  or negedge in[4]  or
          posedge in[5]  or negedge in[5]  or
          posedge in[6]  or negedge in[6]  or
          posedge in[7]  or negedge in[7]  or
          posedge in[8]  or negedge in[8]  or
          posedge in[9]  or negedge in[9]  or
          posedge in[10] or negedge in[10] or
          posedge in[11] or negedge in[11] or
          posedge in[12] or negedge in[12] or
          posedge in[13] or negedge in[13] or
          posedge in[14] or negedge in[14] or
          posedge in[15] or negedge in[15] or
          posedge in[16] or negedge in[16] or
          posedge in[17] or negedge in[17] or
          posedge in[18] or negedge in[18] or
          posedge in[19] or negedge in[19] or
          posedge in[20] or negedge in[20] or
          posedge in[21] or negedge in[21] or
          posedge in[22] or negedge in[22] or
          posedge in[23] or negedge in[23] or
          posedge in[24] or negedge in[24] or
          posedge in[25] or negedge in[25] or
          posedge in[26] or negedge in[26] or
          posedge in[27] or negedge in[27] or
          posedge in[28] or negedge in[28] or
          posedge in[29] or negedge in[29] or
          posedge in[30] or negedge in[30] or
          posedge in[31] or negedge in[31] or
          posedge out    or negedge out)
        (!$initstate && $onehot(in ^ $past(in))) |-> (out != $past(out))
    );

    // Output toggle equals parity of input toggles since last sample.
    check_parity_of_differences: assert property (
        @(posedge in[0]  or negedge in[0]  or
          posedge in[1]  or negedge in[1]  or
          posedge in[2]  or negedge in[2]  or
          posedge in[3]  or negedge in[3]  or
          posedge in[4]  or negedge in[4]  or
          posedge in[5]  or negedge in[5]  or
          posedge in[6]  or negedge in[6]  or
          posedge in[7]  or negedge in[7]  or
          posedge in[8]  or negedge in[8]  or
          posedge in[9]  or negedge in[9]  or
          posedge in[10] or negedge in[10] or
          posedge in[11] or negedge in[11] or
          posedge in[12] or negedge in[12] or
          posedge in[13] or negedge in[13] or
          posedge in[14] or negedge in[14] or
          posedge in[15] or negedge in[15] or
          posedge in[16] or negedge in[16] or
          posedge in[17] or negedge in[17] or
          posedge in[18] or negedge in[18] or
          posedge in[19] or negedge in[19] or
          posedge in[20] or negedge in[20] or
          posedge in[21] or negedge in[21] or
          posedge in[22] or negedge in[22] or
          posedge in[23] or negedge in[23] or
          posedge in[24] or negedge in[24] or
          posedge in[25] or negedge in[25] or
          posedge in[26] or negedge in[26] or
          posedge in[27] or negedge in[27] or
          posedge in[28] or negedge in[28] or
          posedge in[29] or negedge in[29] or
          posedge in[30] or negedge in[30] or
          posedge in[31] or negedge in[31] or
          posedge out    or negedge out)
        (!$initstate) |-> ((out ^ $past(out)) == ^(in ^ $past(in)))
    );

endmodule