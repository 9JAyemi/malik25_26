module template_periph_8b_sva #(
    parameter [14:0] BASE_ADDR = 15'h0090,
    parameter        DEC_WD    = 2,
    parameter [DEC_WD-1:0] CNTRL1 = 'h0,
    parameter [DEC_WD-1:0] CNTRL2 = 'h1,
    parameter [DEC_WD-1:0] CNTRL3 = 'h2,
    parameter [DEC_WD-1:0] CNTRL4 = 'h3
) (
    input logic [15:0] per_dout,
    input logic        mclk,
    input logic [13:0] per_addr,
    input logic [15:0] per_din,
    input logic        per_en,
    input logic [1:0]  per_we,
    input logic        puc_rst,

    input logic                        reg_sel,
    input logic [DEC_WD-1:0]           reg_addr,
    input logic [(1<<DEC_WD)-1:0]      reg_dec,
    input logic                        reg_lo_write,
    input logic                        reg_hi_write,
    input logic                        reg_read,
    input logic [(1<<DEC_WD)-1:0]      reg_hi_wr,
    input logic [(1<<DEC_WD)-1:0]      reg_lo_wr,
    input logic [(1<<DEC_WD)-1:0]      reg_rd,

    input logic [7:0]                  cntrl1,
    input logic                        cntrl1_wr,
    input logic [7:0]                  cntrl1_nxt,
    input logic [7:0]                  cntrl2,
    input logic                        cntrl2_wr,
    input logic [7:0]                  cntrl2_nxt,
    input logic [7:0]                  cntrl3,
    input logic                        cntrl3_wr,
    input logic [7:0]                  cntrl3_nxt,
    input logic [7:0]                  cntrl4,
    input logic                        cntrl4_wr,
    input logic [7:0]                  cntrl4_nxt
);

    localparam int DEC_SZ = (1 << DEC_WD);
    localparam [DEC_SZ-1:0] BASE_REG = {{DEC_SZ-1{1'b0}}, 1'b1};
    localparam [DEC_SZ-1:0] CNTRL1_D = (BASE_REG << CNTRL1);
    localparam [DEC_SZ-1:0] CNTRL2_D = (BASE_REG << CNTRL2);
    localparam [DEC_SZ-1:0] CNTRL3_D = (BASE_REG << CNTRL3);
    localparam [DEC_SZ-1:0] CNTRL4_D = (BASE_REG << CNTRL4);

    // Reset clears all four control bytes.
    reset_clears_control_regs: assert property (
        @(posedge mclk)
        puc_rst |-> (cntrl1 == 8'h00) && (cntrl2 == 8'h00) && (cntrl3 == 8'h00) && (cntrl4 == 8'h00)
    );

    // Register select matches the peripheral base address decode.
    check_reg_select_decode: assert property (
        @(posedge mclk) disable iff (puc_rst)
        reg_sel == (per_en & (per_addr[13:DEC_WD-1] == BASE_ADDR[14:DEC_WD]))
    );

    // Register address is the zero-extended low address field.
    check_reg_address_decode: assert property (
        @(posedge mclk) disable iff (puc_rst)
        reg_addr == {1'b0, per_addr[DEC_WD-2:0]}
    );

    // Register decode matches the two-word control map.
    check_register_decode_map: assert property (
        @(posedge mclk) disable iff (puc_rst)
        reg_dec == ((CNTRL1_D & {DEC_SZ{(reg_addr == (CNTRL1 >> 1))}}) |
                    (CNTRL2_D & {DEC_SZ{(reg_addr == (CNTRL2 >> 1))}}) |
                    (CNTRL3_D & {DEC_SZ{(reg_addr == (CNTRL3 >> 1))}}) |
                    (CNTRL4_D & {DEC_SZ{(reg_addr == (CNTRL4 >> 1))}}))
    );

    // Read and write qualifiers come directly from per_we and reg_sel.
    check_access_qualifiers: assert property (
        @(posedge mclk) disable iff (puc_rst)
        (reg_lo_write == (per_we[0] & reg_sel)) &&
        (reg_hi_write == (per_we[1] & reg_sel)) &&
        (reg_read     == ((~|per_we) & reg_sel))
    );

    // Masked decode vectors are gated versions of reg_dec.
    check_mask_generation: assert property (
        @(posedge mclk) disable iff (puc_rst)
        (reg_hi_wr == (reg_dec & {DEC_SZ{reg_hi_write}})) &&
        (reg_lo_wr == (reg_dec & {DEC_SZ{reg_lo_write}})) &&
        (reg_rd    == (reg_dec & {DEC_SZ{reg_read}}))
    );

    // cntrl1 write strobe and data select the proper byte lane.
    check_cntrl1_write_path: assert property (
        @(posedge mclk) disable iff (puc_rst)
        (cntrl1_wr  == (CNTRL1[0] ? reg_hi_wr[CNTRL1] : reg_lo_wr[CNTRL1])) &&
        (cntrl1_nxt == (CNTRL1[0] ? per_din[15:8]     : per_din[7:0]))
    );

    // cntrl1 follows its write enable and otherwise holds value.
    check_cntrl1_state_update: assert property (
        @(posedge mclk) disable iff (puc_rst)
        1'b1 |=> cntrl1 == ($past(cntrl1_wr) ? $past(cntrl1_nxt) : $past(cntrl1))
    );

    // cntrl2 write strobe and data select the proper byte lane.
    check_cntrl2_write_path: assert property (
        @(posedge mclk) disable iff (puc_rst)
        (cntrl2_wr  == (CNTRL2[0] ? reg_hi_wr[CNTRL2] : reg_lo_wr[CNTRL2])) &&
        (cntrl2_nxt == (CNTRL2[0] ? per_din[15:8]     : per_din[7:0]))
    );

    // cntrl2 follows its write enable and otherwise holds value.
    check_cntrl2_state_update: assert property (
        @(posedge mclk) disable iff (puc_rst)
        1'b1 |=> cntrl2 == ($past(cntrl2_wr) ? $past(cntrl2_nxt) : $past(cntrl2))
    );

    // cntrl3 write strobe and data select the proper byte lane.
    check_cntrl3_write_path: assert property (
        @(posedge mclk) disable iff (puc_rst)
        (cntrl3_wr  == (CNTRL3[0] ? reg_hi_wr[CNTRL3] : reg_lo_wr[CNTRL3])) &&
        (cntrl3_nxt == (CNTRL3[0] ? per_din[15:8]     : per_din[7:0]))
    );

    // cntrl3 follows its write enable and otherwise holds value.
    check_cntrl3_state_update: assert property (
        @(posedge mclk) disable iff (puc_rst)
        1'b1 |=> cntrl3 == ($past(cntrl3_wr) ? $past(cntrl3_nxt) : $past(cntrl3))
    );

    // cntrl4 write strobe and data select the proper byte lane.
    check_cntrl4_write_path: assert property (
        @(posedge mclk) disable iff (puc_rst)
        (cntrl4_wr  == (CNTRL4[0] ? reg_hi_wr[CNTRL4] : reg_lo_wr[CNTRL4])) &&
        (cntrl4_nxt == (CNTRL4[0] ? per_din[15:8]     : per_din[7:0]))
    );

    // cntrl4 follows its write enable and otherwise holds value.
    check_cntrl4_state_update: assert property (
        @(posedge mclk) disable iff (puc_rst)
        1'b1 |=> cntrl4 == ($past(cntrl4_wr) ? $past(cntrl4_nxt) : $past(cntrl4))
    );

    // Reads of the first word return cntrl2:cntrl1.
    check_readback_low_word: assert property (
        @(posedge mclk) disable iff (puc_rst)
        (reg_rd[CNTRL1] && reg_rd[CNTRL2]) |-> (per_dout == {cntrl2, cntrl1})
    );

    // Reads of the second word return cntrl4:cntrl3.
    check_readback_high_word: assert property (
        @(posedge mclk) disable iff (puc_rst)
        (reg_rd[CNTRL3] && reg_rd[CNTRL4]) |-> (per_dout == {cntrl4, cntrl3})
    );

    // Non-read cycles must not drive peripheral read data.
    check_nonread_dout_zero: assert property (
        @(posedge mclk) disable iff (puc_rst)
        !reg_read |-> (per_dout == 16'h0000)
    );

endmodule

bind template_periph_8b template_periph_8b_sva #(
    .BASE_ADDR(BASE_ADDR),
    .DEC_WD(DEC_WD),
    .CNTRL1(CNTRL1),
    .CNTRL2(CNTRL2),
    .CNTRL3(CNTRL3),
    .CNTRL4(CNTRL4)
) template_periph_8b_sva_inst (
    .per_dout(per_dout),
    .mclk(mclk),
    .per_addr(per_addr),
    .per_din(per_din),
    .per_en(per_en),
    .per_we(per_we),
    .puc_rst(puc_rst),
    .reg_sel(reg_sel),
    .reg_addr(reg_addr),
    .reg_dec(reg_dec),
    .reg_lo_write(reg_lo_write),
    .reg_hi_write(reg_hi_write),
    .reg_read(reg_read),
    .reg_hi_wr(reg_hi_wr),
    .reg_lo_wr(reg_lo_wr),
    .reg_rd(reg_rd),
    .cntrl1(cntrl1),
    .cntrl1_wr(cntrl1_wr),
    .cntrl1_nxt(cntrl1_nxt),
    .cntrl2(cntrl2),
    .cntrl2_wr(cntrl2_wr),
    .cntrl2_nxt(cntrl2_nxt),
    .cntrl3(cntrl3),
    .cntrl3_wr(cntrl3_wr),
    .cntrl3_nxt(cntrl3_nxt),
    .cntrl4(cntrl4),
    .cntrl4_wr(cntrl4_wr),
    .cntrl4_nxt(cntrl4_nxt)
);