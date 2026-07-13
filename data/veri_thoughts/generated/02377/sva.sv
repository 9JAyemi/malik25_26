module top_module_sva (
    input logic [31:0] in,
    input logic        select,
    input logic [31:0] out
);
    // On select rising edge, out must equal in.
    check_out_eq_in_on_select_rise: assert property (
        @(posedge select) out == in
    );

    // On select falling edge, out must be all zeros.
    check_out_zero_on_select_fall: assert property (
        @(negedge select) out == 32'h0
    );

    // Out equals masked form {32{select}} & in on in[0] rising edge.
    check_mask_equivalence_pos_in0: assert property (
        @(posedge in[0]) out == ({32{select}} & in)
    );

    // Out equals masked form {32{select}} & in on in[0] falling edge.
    check_mask_equivalence_neg_in0: assert property (
        @(negedge in[0]) out == ({32{select}} & in)
    );

    // Out has no bits set outside of in (subset) on in[1] rising edge.
    check_out_subset_of_in: assert property (
        @(posedge in[1]) (out & ~in) == 32'h0
    );

    // OR with in returns in on in[2] rising edge.
    check_out_or_in_equals_in: assert property (
        @(posedge in[2]) (out | in) == in
    );

    // XOR relation: out ^ in equals (~select) mask of in on in[3] rising edge.
    check_xor_relation: assert property (
        @(posedge in[3]) (out ^ in) == ({32{~select}} & in)
    );

    // Nonzero out implies select is HIGH on in[4] rising edge.
    check_nonzero_out_implies_select: assert property (
        @(posedge in[4]) (|out) |-> (select == 1'b1)
    );

    // When select is LOW, out must be zero on in[5] rising edge.
    check_select_low_implies_zero_pos_in5: assert property (
        @(posedge in[5]) (select == 1'b0) |-> (out == 32'h0)
    );

    // When select is LOW, out must be zero on in[5] falling edge.
    check_select_low_implies_zero_neg_in5: assert property (
        @(negedge in[5]) (select == 1'b0) |-> (out == 32'h0)
    );

    // When select is HIGH, out equals in on in[6] rising edge.
    check_select_high_implies_out_eq_in: assert property (
        @(posedge in[6]) (select == 1'b1) |-> (out == in)
    );

    // Out is idempotent with in: (out & in) == out on in[7] rising edge.
    check_out_idempotent_with_in: assert property (
        @(posedge in[7]) (out & in) == out
    );
endmodule