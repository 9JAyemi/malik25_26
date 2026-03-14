module key_gen_sva (
    input logic clk,
    input logic reset,
    input logic p2k_valid,
    input logic [7:0] p2k_ingress,
    input logic [127:0] p2k_rloc_src,
    input logic [127:0] p2k_eid_dst,
    input logic [7:0] p2k_metadata,
    input logic mode,
    input logic k2m_metadata_valid,
    input logic [107:0] k2m_metadata
);
    // During active-low reset, outputs are driven to zero.
    reset_outputs_zero: assert property (
        @(posedge clk) !reset |-> (k2m_metadata_valid == 1'b0) && (k2m_metadata == 108'b0)
    );

    // When p2k_valid is HIGH, k2m_metadata_valid is HIGH next cycle.
    valid_next_high_when_p2k_valid: assert property (
        @(posedge clk) disable iff (!reset) (p2k_valid == 1'b1) |=> (k2m_metadata_valid == 1'b1)
    );

    // When p2k_valid is LOW, k2m_metadata_valid is LOW next cycle.
    valid_next_low_when_no_p2k_valid: assert property (
        @(posedge clk) disable iff (!reset) (p2k_valid == 1'b0) |=> (k2m_metadata_valid == 1'b0)
    );

    // On p2k_valid & mode & ingress==0, metadata captures mode, ingress, rloc[17:0], zeros.
    metadata_mode1_ingress0_content: assert property (
        @(posedge clk) disable iff (!reset)
            (p2k_valid && (mode == 1'b1) && (p2k_ingress == 8'b0)) |=> 
            (k2m_metadata_valid == 1'b1) &&
            (k2m_metadata == {mode, p2k_ingress, p2k_rloc_src[17:0], 81'b0})
    );

    // On p2k_valid & mode & ingress!=0, metadata captures mode, ingress, zeros, zeros.
    metadata_mode1_ingressnz_content: assert property (
        @(posedge clk) disable iff (!reset)
            (p2k_valid && (mode == 1'b1) && (p2k_ingress != 8'b0)) |=> 
            (k2m_metadata_valid == 1'b1) &&
            (k2m_metadata == {mode, p2k_ingress, 18'b0, 81'b0})
    );

    // On p2k_valid & !mode, metadata equals truncated {mode,ingress,eid[127:56],56'b0}.
    metadata_mode0_truncated_eid: assert property (
        @(posedge clk) disable iff (!reset)
            (p2k_valid && (mode == 1'b0)) |=> 
            (k2m_metadata_valid == 1'b1) &&
            (k2m_metadata == {p2k_eid_dst[107:56], 56'b0})
    );

    // When p2k_valid is LOW, metadata holds its previous value.
    metadata_holds_when_no_valid: assert property (
        @(posedge clk) disable iff (!reset)
            (p2k_valid == 1'b0) |=> (k2m_metadata == $past(k2m_metadata))
    );

    // For mode==1 updates, low 81 bits of metadata are zero next cycle.
    mode1_low81_zero: assert property (
        @(posedge clk) disable iff (!reset)
            (p2k_valid && (mode == 1'b1)) |=> (k2m_metadata[80:0] == 81'b0)
    );

    // For mode==1 updates, ingress is reflected in bits [106:99] next cycle.
    mode1_carries_ingress_bits: assert property (
        @(posedge clk) disable iff (!reset)
            (p2k_valid && (mode == 1'b1)) |=> (k2m_metadata[106:99] == p2k_ingress)
    );

    // For mode==0 updates, low 56 bits of metadata are zero next cycle.
    mode0_low56_zero: assert property (
        @(posedge clk) disable iff (!reset)
            (p2k_valid && (mode == 1'b0)) |=> (k2m_metadata[55:0] == 56'b0)
    );
endmodule