module adc_transformer_sva (
    input logic [14-1:0] adc_dat_a_i,
    input logic [14-1:0] adc_dat_b_i,
    input logic          adc_clk,
    input logic [2-1:0]  adc_clk_source,
    input logic          adc_cdcs_o,
    input logic [14-1:0] adc_dat_a_o,
    input logic [14-1:0] adc_dat_b_o,
    input logic          adc_rst_i
);

// adc_cdcs_o is driven HIGH.
    check_cdcs_high: assert property (
        @(posedge adc_clk) disable iff (!adc_rst_i) adc_cdcs_o == 1'b1
    );

// adc_clk_source is driven to 2'b10.
    check_clk_source_fixed: assert property (
        @(posedge adc_clk) disable iff (!adc_rst_i) adc_clk_source == 2'b10
    );

// adc_dat_a_o is the 2's complement of the previous cycle's adc_dat_a_i.
    check_dat_a_twos_complement: assert property (
        @(posedge adc_clk) disable iff (!adc_rst_i)
            1'b1 |=> (adc_dat_a_o == {~$past(adc_dat_a_i[14-1]), $past(adc_dat_a_i[14-2:0])})
    );

// adc_dat_b_o is the 2's complement of the previous cycle's adc_dat_b_i.
    check_dat_b_twos_complement: assert property (
        @(posedge adc_clk) disable iff (!adc_rst_i)
            1'b1 |=> (adc_dat_b_o == {~$past(adc_dat_b_i[14-1]), $past(adc_dat_b_i[14-2:0])})
    );

// adc_dat_a_o[14] is the bitwise inversion of the previous cycle's adc_dat_a_i[14].
    check_dat_a_msb_inversion: assert property (
        @(posedge adc_clk) disable iff (!adc_rst_i)
            1'b1 |=> (adc_dat_a_o[14] == ~$past(adc_dat_a_i[14]))
    );

// adc_dat_a_o[13:0] is the bitwise inversion of the previous cycle's adc_dat_a_i[13:0].
    check_dat_a_lsb_inversion: assert property (
        @(posedge adc_clk) disable iff (!adc_rst_i)
            1'b1 |=> (adc_dat_a_o[13:0] == ~$past(adc_dat_a_i[13:0]))
    );

// adc_dat_b_o[14] is the bitwise inversion of the previous cycle's adc_dat_b_i[14].
    check_dat_b_msb_inversion: assert property (
        @(posedge adc_clk) disable iff (!adc_rst_i)
            1'b1 |=> (adc_dat_b_o[14] == ~$past(adc_dat_b_i[14]))
    );

// adc_dat_b_o[13:0] is the bitwise inversion of the previous cycle's adc_dat_b_i[13:0].
    check_dat_b_lsb_inversion: assert property (
        @(posedge adc_clk) disable iff (!adc_rst_i)
            1'b1 |=> (adc_dat_b_o[13:0] == ~$past(adc_dat_b_i[13:0]))
    );

endmodule
