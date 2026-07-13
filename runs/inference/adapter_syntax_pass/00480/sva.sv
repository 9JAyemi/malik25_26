module adc_transformer_sva (
    input logic [13:0] adc_dat_a_i,
    input logic [13:0] adc_dat_b_i,
    input logic        adc_clk,
    input logic [1:0]  adc_clk_source,
    input logic        adc_cdcs_o,
    input logic [13:0] adc_dat_a_o,
    input logic [13:0] adc_dat_b_o,
    input logic        adc_rst_i
);

    // adc_cdcs_o is tied high.
    check_cdcs_tied_high: assert property (
        @(posedge adc_clk) disable iff (adc_rst_i)
        (adc_cdcs_o == 1'b1)
    );

    // adc_clk_source is tied to 2'b10.
    check_clk_source_tied_value: assert property (
        @(posedge adc_clk) disable iff (adc_rst_i)
        (adc_clk_source == 2'b10)
    );

    // adc_dat_a_o is the 2's complement of the previous cycle's adc_dat_a_i.
    check_dat_a_transform: assert property (
        @(posedge adc_clk) disable iff (adc_rst_i)
        1'b1 |=> (adc_dat_a_o == {1'b0, ~$past(adc_dat_a_i[12:0])})
    );

    // adc_dat_b_o is the 2's complement of the previous cycle's adc_dat_b_i.
    check_dat_b_transform: assert property (
        @(posedge adc_clk) disable iff (adc_rst_i)
        1'b1 |=> (adc_dat_b_o == {1'b0, ~$past(adc_dat_b_i[12:0])})
    );

    // adc_dat_a_o[13] is always zero.
    check_dat_a_msb_zero: assert property (
        @(posedge adc_clk) disable iff (adc_rst_i)
        (adc_dat_a_o[13] == 1'b0)
    );

    // adc_dat_b_o[13] is always zero.
    check_dat_b_msb_zero: assert property (
        @(posedge adc_clk) disable iff (adc_rst_i)
        (adc_dat_b_o[13] == 1'b0)
    );

    // adc_dat_a_o[12] is the inverse of the previous cycle's adc_dat_a_i[12].
    check_dat_a_bit12_inverts: assert property (
        @(posedge adc_clk) disable iff (adc_rst_i)
        1'b1 |=> (adc_dat_a_o[12] == ~$past(adc_dat_a_i[12]))
    );

    // adc_dat_b_o[12] is the inverse of the previous cycle's adc_dat_b_i[12].
    check_dat_b_bit12_inverts: assert property (
        @(posedge adc_clk) disable iff (adc_rst_i)
        1'b1 |=> (adc_dat_b_o[12] == ~$past(adc_dat_b_i[12]))
    );

    // adc_dat_a_o[11:0] is the bitwise inverse of the previous cycle's adc_dat_a_i[11:0].
    check_dat_a_low_bits_invert: assert property (
        @(posedge adc_clk) disable iff (adc_rst_i)
        1'b1 |=> (adc_dat_a_o[11:0] == ~$past(adc_dat_a_i[11:0]))
    );

    // adc_dat_b_o[11:0] is the bitwise inverse of the previous cycle's adc_dat_b_i[11:0].
    check_dat_b_low_bits_invert: assert property (
        @(posedge adc_clk) disable iff (adc_rst_i)
        1'b1 |=> (adc_dat_b_o[11:0] == ~$past(adc_dat_b_i[11:0]))
    );

endmodule