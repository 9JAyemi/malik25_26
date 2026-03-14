module top_module_sva (
    input logic clk,
    input logic [255:0] in,
    input logic [7:0] sel,
    input logic out,

    // Internal signals from DUT (bind hierarchically)
    input logic [7:0] decoder_out,
    input logic [1:0] mux2_out
);

    ///// Decoder checks /////
    // Decoder outputs sel when sel is one-hot.
    decoder_matches_onehot_sel: assert property (
        @(posedge clk) $onehot(sel) |-> (decoder_out == sel)
    );

    // Decoder outputs 0 when sel is not one-hot.
    decoder_zero_when_not_onehot: assert property (
        @(posedge clk) !$onehot(sel) |-> (decoder_out == 8'b0)
    );

    // Decoder output is always one-hot or zero.
    decoder_out_onehot0: assert property (
        @(posedge clk) $onehot0(decoder_out)
    );

    ///// mux2 checks /////
    // When sel[0]==0, mux2_out replicates in[decoder_out + 1].
    mux2_sel0_replication: assert property (
        @(posedge clk) (sel[0] == 1'b0) |-> (mux2_out == {in[decoder_out + 1], in[decoder_out + 1]})
    );

    // When sel[0]==1, mux2_out replicates in[decoder_out].
    mux2_sel1_replication: assert property (
        @(posedge clk) (sel[0] == 1'b1) |-> (mux2_out == {in[decoder_out], in[decoder_out]})
    );

    // mux2_out bits are always identical.
    mux2_bits_identical: assert property (
        @(posedge clk) (mux2_out[1] == mux2_out[0])
    );

    ///// Final mux checks /////
    // Final mux selects mux2_out bit indexed by sel[0].
    final_mux_select: assert property (
        @(posedge clk) (out == mux2_out[sel[0]])
    );

    // End-to-end: out equals selected input bit.
    end_to_end_out_value: assert property (
        @(posedge clk) out == (sel[0] ? in[decoder_out] : in[decoder_out + 1])
    );

    // When sel[0]==0, out equals in[decoder_out + 1].
    end_to_end_sel0: assert property (
        @(posedge clk) (sel[0] == 1'b0) |-> (out == in[decoder_out + 1])
    );

    // When sel[0]==1, out equals in[decoder_out].
    end_to_end_sel1: assert property (
        @(posedge clk) (sel[0] == 1'b1) |-> (out == in[decoder_out])
    );

endmodule