module switch_bit_sva (
    input logic CLK,
    input logic [3:0] gpio_sel,
    input logic [7:0] tri_i_in,
    input logic [7:0] tri_o_in,
    input logic [7:0] tri_t_in,
    input logic tri_i_out,
    input logic tri_o_out,
    input logic tri_t_out,
    input logic pwm_i_in,
    input logic pwm_o_in,
    input logic pwm_t_in,
    input logic cap0_i_in,
    input logic gen0_o_in,
    input logic gen0_t_in,
    input logic spick_i_in,
    input logic spick_o_in,
    input logic spick_t_in,
    input logic miso_i_in,
    input logic miso_o_in,
    input logic miso_t_in,
    input logic mosi_i_in,
    input logic mosi_o_in,
    input logic mosi_t_in,
    input logic ss_i_in,
    input logic ss_o_in,
    input logic ss_t_in,
    input logic sda_i_in,
    input logic sda_o_in,
    input logic sda_t_in,
    input logic scl_i_in,
    input logic scl_o_in,
    input logic scl_t_in
);
    // tri_o_out implements mux per gpio_sel.
    check_tri_o_out_mux: assert property (
        @(posedge CLK)
        tri_o_out ==
            ((gpio_sel <= 4'h7) ? tri_o_in[gpio_sel] :
            (gpio_sel == 4'h8) ? scl_o_in :
            (gpio_sel == 4'h9) ? sda_o_in :
            (gpio_sel == 4'hA) ? spick_o_in :
            (gpio_sel == 4'hB) ? miso_o_in :
            (gpio_sel == 4'hC) ? mosi_o_in :
            (gpio_sel == 4'hD) ? ss_o_in   :
            (gpio_sel == 4'hE) ? pwm_o_in  :
            (gpio_sel == 4'hF) ? gen0_o_in :
            1'b0)
    );

    // tri_t_out implements mux per gpio_sel.
    check_tri_t_out_mux: assert property (
        @(posedge CLK)
        tri_t_out ==
            ((gpio_sel <= 4'h7) ? tri_t_in[gpio_sel] :
            (gpio_sel == 4'h8) ? scl_t_in :
            (gpio_sel == 4'h9) ? sda_t_in :
            (gpio_sel == 4'hA) ? spick_t_in :
            (gpio_sel == 4'hB) ? miso_t_in :
            (gpio_sel == 4'hC) ? mosi_t_in :
            (gpio_sel == 4'hD) ? ss_t_in   :
            (gpio_sel == 4'hE) ? pwm_t_in  :
            (gpio_sel == 4'hF) ? gen0_t_in :
            1'b0)
    );

    // tri_i_in drives one-hot bit (sel) with tri_i_out when sel<8.
    check_tri_i_in_sel_lt8: assert property (
        @(posedge CLK)
        (gpio_sel <= 4'h7) |-> (tri_i_in == ((8'b0000_0001 << gpio_sel) & {8{tri_i_out}}))
    );

    // tri_i_in is zero when sel>=8.
    check_tri_i_in_sel_ge8_zero: assert property (
        @(posedge CLK)
        (gpio_sel >= 4'h8) |-> (tri_i_in == 8'h00)
    );

    // scl_i_in equals tri_i_out when selected (sel==8).
    check_scl_i_in_select: assert property (
        @(posedge CLK)
        (gpio_sel == 4'h8) |-> (scl_i_in == tri_i_out)
    );

    // sda_i_in equals tri_i_out when selected (sel==9).
    check_sda_i_in_select: assert property (
        @(posedge CLK)
        (gpio_sel == 4'h9) |-> (sda_i_in == tri_i_out)
    );

    // spick_i_in equals tri_i_out when selected (sel==A).
    check_spick_i_in_select: assert property (
        @(posedge CLK)
        (gpio_sel == 4'hA) |-> (spick_i_in == tri_i_out)
    );

    // miso_i_in equals tri_i_out when selected (sel==B).
    check_miso_i_in_select: assert property (
        @(posedge CLK)
        (gpio_sel == 4'hB) |-> (miso_i_in == tri_i_out)
    );

    // mosi_i_in equals tri_i_out when selected (sel==C).
    check_mosi_i_in_select: assert property (
        @(posedge CLK)
        (gpio_sel == 4'hC) |-> (mosi_i_in == tri_i_out)
    );

    // ss_i_in equals tri_i_out when selected (sel==D).
    check_ss_i_in_select: assert property (
        @(posedge CLK)
        (gpio_sel == 4'hD) |-> (ss_i_in == tri_i_out)
    );

    // pwm_i_in equals tri_i_out when selected (sel==E).
    check_pwm_i_in_select: assert property (
        @(posedge CLK)
        (gpio_sel == 4'hE) |-> (pwm_i_in == tri_i_out)
    );

    // cap0_i_in equals tri_i_out when selected (sel==F).
    check_cap0_i_in_select: assert property (
        @(posedge CLK)
        (gpio_sel == 4'hF) |-> (cap0_i_in == tri_i_out)
    );

    // Demux outputs are exactly one-hot when tri_i_out==1.
    check_demux_onehot_when_1: assert property (
        @(posedge CLK)
        (tri_i_out == 1'b1) |-> $onehot({cap0_i_in, pwm_i_in, ss_i_in, mosi_i_in, miso_i_in, spick_i_in, sda_i_in, scl_i_in, tri_i_in})
    );

    // Demux outputs are all zero when tri_i_out==0.
    check_demux_all_zero_when_0: assert property (
        @(posedge CLK)
        (tri_i_out == 1'b0) |-> ({cap0_i_in, pwm_i_in, ss_i_in, mosi_i_in, miso_i_in, spick_i_in, sda_i_in, scl_i_in, tri_i_in} == 16'h0000)
    );
endmodule