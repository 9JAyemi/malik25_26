module adc_transformer_sva (
    input logic adc_clk,
    input logic adc_rst_i,
    input logic [14-1: 0] adc_dat_a_i,
    input logic [14-1: 0] adc_dat_b_i,
    output logic [2-1: 0] adc_clk_source,
    output logic adc_cdcs_o,
    output logic [14-1: 0] adc_dat_a_o,
    output logic [14-1: 0] adc_dat_b_o
);
    // ADC clock duty cycle stabilizer is always enabled
    adc_cdcs_o_enabled: assert property (
        @(posedge adc_clk) disable iff (!adc_rst_i) (adc_cdcs_o == 1'b1)
    );

    // Generating ADC clock is always disabled
    adc_clk_source_disabled: assert property (
        @(posedge adc_clk) disable iff (!adc_rst_i) (adc_clk_source == 2'b10)
    );

    // ADC data is updated on the rising edge of the ADC clock
    adc_data_update: assert property (
        @(posedge adc_clk) disable iff (!adc_rst_i) (adc_dat_a == adc_dat_a_i[14-1:0]) && (adc_dat_b == adc_dat_b_i[14-1:0])
    );

    // ADC data output is transformed into 2's complement
    adc_data_transform: assert property (
        @(posedge adc_clk) disable iff (!adc_rst_i) (adc_dat_a_o == {adc_dat_a[14-1], ~adc_dat_a[14-2:0]}) && (adc_dat_b_o == {adc_dat_b[14-1], ~adc_dat_b[14-2:0]})
    );

    // ADC reset drives both outputs LOW
    adc_reset_output: assert property (
        @(posedge adc_clk) !adc_rst_i |-> (adc_dat_a_o == 14'b0) && (adc_dat_b_o == 14'b0)
    );

endmodule