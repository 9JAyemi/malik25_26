module EX_MEM_sva (
    input logic        clk,
    input logic [1:0]  ctlwb_out, 
    input logic [2:0]  ctlm_out,
    input logic [31:0] adder_out,
    input logic        aluzero,
    input logic [31:0] aluout,
    input logic [31:0] readdat2,
    input logic [4:0]  muxout,
    input logic [1:0]  wb_ctlout,
    input logic [2:0]  m_ctlout,
    input logic [31:0] add_result,
    input logic        zero,
    input logic [31:0] alu_result,
    input logic [31:0] rdata2out,
    input logic [4:0]  five_bit_muxout
);

    ///// Pipeline register behavior /////
    // wb_ctlout updates to previous-cycle ctlwb_out.
    check_wb_ctlout_pipeline: assert property (
        @(posedge clk) disable iff ($initstate) wb_ctlout == $past(ctlwb_out)
    );

    // m_ctlout updates to previous-cycle ctlm_out.
    check_m_ctlout_pipeline: assert property (
        @(posedge clk) disable iff ($initstate) m_ctlout == $past(ctlm_out)
    );

    // add_result updates to previous-cycle adder_out.
    check_add_result_pipeline: assert property (
        @(posedge clk) disable iff ($initstate) add_result == $past(adder_out)
    );

    // zero updates to previous-cycle aluzero.
    check_zero_pipeline: assert property (
        @(posedge clk) disable iff ($initstate) zero == $past(aluzero)
    );

    // alu_result updates to previous-cycle aluout.
    check_alu_result_pipeline: assert property (
        @(posedge clk) disable iff ($initstate) alu_result == $past(aluout)
    );

    // rdata2out updates to previous-cycle readdat2.
    check_rdata2out_pipeline: assert property (
        @(posedge clk) disable iff ($initstate) rdata2out == $past(readdat2)
    );

    // five_bit_muxout updates to previous-cycle muxout.
    check_five_bit_muxout_pipeline: assert property (
        @(posedge clk) disable iff ($initstate) five_bit_muxout == $past(muxout)
    );

endmodule