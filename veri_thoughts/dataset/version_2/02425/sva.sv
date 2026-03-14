module execute_load_data_sva (
    input logic CLK,
    input logic [3:0]  iMASK,
    input logic [1:0]  iSHIFT,
    input logic [31:0] iDATA,
    input logic [31:0] oDATA
);
    // oDATA equals the exact combinational function of iMASK/iSHIFT/iDATA.
    check_exact_function: assert property (
        @(posedge CLK) disable iff (1'b0)
        oDATA ==
            ((iSHIFT == 2'b00) ?
                ((iMASK == 4'hf)    ? iDATA :
                 (iMASK == 4'b0001) ? {iDATA[31:24], 24'h0} :
                 (iMASK == 4'b0010) ? {iDATA[23:16], 24'h0} :
                 (iMASK == 4'b0100) ? {iDATA[15:8],  24'h0} :
                 (iMASK == 4'b1000) ? {iDATA[7:0],   24'h0} :
                 (iMASK == 4'b0011) ? {iDATA[31:16], 16'h0} :
                                      {iDATA[31:8],  8'h0})
            : (iSHIFT == 2'b01) ?
                ((iMASK == 4'hf)    ? (iDATA >> 1) :
                 (iMASK == 4'b0001) ? ({iDATA[31:24], 24'h0} >> 1) :
                 (iMASK == 4'b0010) ? ({iDATA[23:16], 24'h0} >> 1) :
                 (iMASK == 4'b0100) ? ({iDATA[15:8],  24'h0} >> 1) :
                 (iMASK == 4'b1000) ? ({iDATA[7:0],   24'h0} >> 1) :
                 (iMASK == 4'b0011) ? ({iDATA[31:16], 16'h0} >> 1) :
                                      ({iDATA[31:8],  8'h0} >> 1))
            : (iSHIFT == 2'b10) ?
                ((iMASK == 4'hf)    ? (iDATA >> 2) :
                 (iMASK == 4'b0001) ? ({iDATA[31:24], 24'h0} >> 2) :
                 (iMASK == 4'b0010) ? ({iDATA[23:16], 24'h0} >> 2) :
                 (iMASK == 4'b0100) ? ({iDATA[15:8],  24'h0} >> 2) :
                 (iMASK == 4'b1000) ? ({iDATA[7:0],   24'h0} >> 2) :
                 (iMASK == 4'b0011) ? ({iDATA[31:16], 16'h0} >> 2) :
                                      ({iDATA[31:8],  8'h0} >> 2))
            :
                ((iMASK == 4'hf)    ? (iDATA >> 3) :
                 (iMASK == 4'b0001) ? ({iDATA[31:24], 24'h0} >> 3) :
                 (iMASK == 4'b0010) ? ({iDATA[23:16], 24'h0} >> 3) :
                 (iMASK == 4'b0100) ? ({iDATA[15:8],  24'h0} >> 3) :
                 (iMASK == 4'b1000) ? ({iDATA[7:0],   24'h0} >> 3) :
                 (iMASK == 4'b0011) ? ({iDATA[31:16], 16'h0} >> 3) :
                                      ({iDATA[31:8],  8'h0} >> 3)))
    );

    // With no shift and mask 1111, pass-through of iDATA.
    check_fullmask_noshift: assert property (
        @(posedge CLK) disable iff (1'b0)
        (iSHIFT == 2'b00 && iMASK == 4'hf) |-> (oDATA == iDATA)
    );

    // With no shift and mask 0001, top byte equals iDATA[31:24], lower 24 bits zero.
    check_mask_0001_noshift: assert property (
        @(posedge CLK) disable iff (1'b0)
        (iSHIFT == 2'b00 && iMASK == 4'b0001) |-> (oDATA[31:24] == iDATA[31:24] && oDATA[23:0] == 24'h0)
    );

    // With no shift and mask 0010, top byte equals iDATA[23:16], lower 24 bits zero.
    check_mask_0010_noshift: assert property (
        @(posedge CLK) disable iff (1'b0)
        (iSHIFT == 2'b00 && iMASK == 4'b0010) |-> (oDATA[31:24] == iDATA[23:16] && oDATA[23:0] == 24'h0)
    );

    // With no shift and mask 0100, top byte equals iDATA[15:8], lower 24 bits zero.
    check_mask_0100_noshift: assert property (
        @(posedge CLK) disable iff (1'b0)
        (iSHIFT == 2'b00 && iMASK == 4'b0100) |-> (oDATA[31:24] == iDATA[15:8] && oDATA[23:0] == 24'h0)
    );

    // With no shift and mask 1000, top byte equals iDATA[7:0], lower 24 bits zero.
    check_mask_1000_noshift: assert property (
        @(posedge CLK) disable iff (1'b0)
        (iSHIFT == 2'b00 && iMASK == 4'b1000) |-> (oDATA[31:24] == iDATA[7:0] && oDATA[23:0] == 24'h0)
    );

    // With no shift and mask 0011, top halfword equals iDATA[31:16], lower 16 bits zero.
    check_mask_0011_noshift: assert property (
        @(posedge CLK) disable iff (1'b0)
        (iSHIFT == 2'b00 && iMASK == 4'b0011) |-> (oDATA[31:16] == iDATA[31:16] && oDATA[15:0] == 16'h0)
    );

    // With no shift and any other mask, top 24 bits equal iDATA[31:8], low byte zero.
    check_default_mask_noshift: assert property (
        @(posedge CLK) disable iff (1'b0)
        (iSHIFT == 2'b00 &&
         !((iMASK == 4'hf) || (iMASK == 4'b0001) || (iMASK == 4'b0010) ||
           (iMASK == 4'b0100) || (iMASK == 4'b1000) || (iMASK == 4'b0011)))
         |-> (oDATA[31:8] == iDATA[31:8] && oDATA[7:0] == 8'h0)
    );
endmodule