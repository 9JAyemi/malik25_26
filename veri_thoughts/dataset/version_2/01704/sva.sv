module fifo19_rxrealign_sva (
    input  logic        clk,
    input  logic        reset,
    input  logic        clear,
    input  logic [18:0] datain,
    input  logic        src_rdy_i,
    input  logic        dst_rdy_o,
    input  logic [18:0] dataout,
    input  logic        src_rdy_o,
    input  logic        dst_rdy_i
);

    ///// Data mapping checks /////
    // dataout[18] must pass through datain[18].
    check_dataout18_passthrough: assert property (
        @(posedge clk) disable iff (reset || clear) dataout[18] == datain[18]
    );
    // dataout[17] must pass through datain[17].
    check_dataout17_passthrough: assert property (
        @(posedge clk) disable iff (reset || clear) dataout[17] == datain[17]
    );
    // dataout[15:0] must pass through datain[15:0].
    check_dataout_lo16_passthrough: assert property (
        @(posedge clk) disable iff (reset || clear) dataout[15:0] == datain[15:0]
    );
    // If datain[17] & datain[16] are 1, dataout[16] must be 1.
    check_dataout16_when_17and16_set: assert property (
        @(posedge clk) disable iff (reset || clear) (datain[17] && datain[16]) |-> (dataout[16] == 1'b1)
    );

    ///// Ready signal relationships /////
    // src_rdy_o must equal src_rdy_i & dst_rdy_i.
    check_src_rdy_o_definition: assert property (
        @(posedge clk) disable iff (reset || clear) src_rdy_o == (src_rdy_i & dst_rdy_i)
    );
    // If src_rdy_i is 0, src_rdy_o must be 0.
    check_src_rdy_o_zero_when_src_not_ready: assert property (
        @(posedge clk) disable iff (reset || clear) (!src_rdy_i) |-> (!src_rdy_o)
    );
    // If dst_rdy_i is 0, src_rdy_o must be 0.
    check_src_rdy_o_zero_when_dst_not_ready: assert property (
        @(posedge clk) disable iff (reset || clear) (!dst_rdy_i) |-> (!src_rdy_o)
    );
    // dst_rdy_o can only be 1 when src_rdy_i & dst_rdy_i are 1.
    check_dst_rdy_o_implies_handshake: assert property (
        @(posedge clk) disable iff (reset || clear) dst_rdy_o |-> (src_rdy_i & dst_rdy_i)
    );
    // dst_rdy_o implies src_rdy_o (since src_rdy_o = src_rdy_i & dst_rdy_i).
    check_dst_rdy_o_subset_src_rdy_o: assert property (
        @(posedge clk) disable iff (reset || clear) dst_rdy_o |-> src_rdy_o
    );
    // If src_rdy_i is 0, dst_rdy_o must be 0.
    check_dst_rdy_o_zero_when_src_not_ready: assert property (
        @(posedge clk) disable iff (reset || clear) (!src_rdy_i) |-> (!dst_rdy_o)
    );
    // If dst_rdy_i is 0, dst_rdy_o must be 0.
    check_dst_rdy_o_zero_when_dst_not_ready: assert property (
        @(posedge clk) disable iff (reset || clear) (!dst_rdy_i) |-> (!dst_rdy_o)
    );

endmodule