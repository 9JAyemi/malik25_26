module decalper_eb_ot_sdeen_pot_pi_dehcac_xnilix_memory_sva (
    dout,
    clk,
    ram_full_fb_i_reg,
    tmp_ram_rd_en,
    out,
    \gcc0.gc0.count_d1_reg[10] ,
    Q,
    din
);

    input logic [63:0] dout;
    input logic clk;
    input logic ram_full_fb_i_reg;
    input logic tmp_ram_rd_en;
    input logic [0:0] out;
    input logic [10:0] \gcc0.gc0.count_d1_reg[10] ;
    input logic [10:0] Q;
    input logic [63:0] din;

    // When full and not reading, dout loads din on the next clock.
    check_dout_loads_din_when_selected: assert property (
        @(posedge clk)
        (ram_full_fb_i_reg && !tmp_ram_rd_en) |=> (dout == $past(din))
    );

    // When not full, dout loads zero-extended Q on the next clock.
    check_dout_loads_q_when_not_full: assert property (
        @(posedge clk)
        (!ram_full_fb_i_reg) |=> (dout == {53'b0, $past(Q)})
    );

    // When read enable is high, dout loads zero-extended Q on the next clock.
    check_dout_loads_q_when_read_enabled: assert property (
        @(posedge clk)
        (ram_full_fb_i_reg && tmp_ram_rd_en) |=> (dout == {53'b0, $past(Q)})
    );

    // On the Q path, the upper bits of dout are zero due to width extension.
    check_q_path_zero_extends_upper_bits: assert property (
        @(posedge clk)
        (!ram_full_fb_i_reg || tmp_ram_rd_en) |=> (dout[63:11] == 53'b0)
    );

    // On the Q path, the low 11 bits of dout match Q.
    check_q_path_preserves_q_low_bits: assert property (
        @(posedge clk)
        (!ram_full_fb_i_reg || tmp_ram_rd_en) |=> (dout[10:0] == $past(Q))
    );

    // Each cycle, dout matches the source selected on the previous clock.
    check_dout_matches_selected_source: assert property (
        @(posedge clk)
        1'b1 |=> (
            (($past(ram_full_fb_i_reg) && !$past(tmp_ram_rd_en)) && (dout == $past(din))) ||
            ((!$past(ram_full_fb_i_reg) || $past(tmp_ram_rd_en)) && (dout == {53'b0, $past(Q)}))
        )
    );

endmodule