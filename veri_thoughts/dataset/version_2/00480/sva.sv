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

    // Duty-cycle stabilizer output is tied high.
    check_adc_cdcs_constant_high: assert property (
        @(posedge adc_clk) disable iff (!adc_rst_i)
        adc_cdcs_o == 1'b1
    );

    // ADC clock source output is tied to 2'b10.
    check_adc_clk_source_constant: assert property (
        @(posedge adc_clk) disable iff (!adc_rst_i)
        adc_clk_source == 2'b10
    );

    // Channel A output matches the prior sampled input transform.
    check_adc_dat_a_transform: assert property (
        @(posedge adc_clk) disable iff (!adc_rst_i)
        1'b1 |=> (adc_dat_a_o == { $past(adc_dat_a_i[13]), ~$past(adc_dat_a_i[12:0]) })
    );

    // Channel B output matches the prior sampled input transform.
    check_adc_dat_b_transform: assert property (
        @(posedge adc_clk) disable iff (!adc_rst_i)
        1'b1 |=> (adc_dat_b_o == { $past(adc_dat_b_i[13]), ~$past(adc_dat_b_i[12:0]) })
    );

    // Channel A sign bit is preserved from the sampled input.
    check_adc_dat_a_sign_preserved: assert property (
        @(posedge adc_clk) disable iff (!adc_rst_i)
        1'b1 |=> (adc_dat_a_o[13] == $past(adc_dat_a_i[13]))
    );

    // Channel A lower bits are inverted from the sampled input.
    check_adc_dat_a_low_bits_inverted: assert property (
        @(posedge adc_clk) disable iff (!adc_rst_i)
        1'b1 |=> (adc_dat_a_o[12:0] == ~$past(adc_dat_a_i[12:0]))
    );

    // Channel B sign bit is preserved from the sampled input.
    check_adc_dat_b_sign_preserved: assert property (
        @(posedge adc_clk) disable iff (!adc_rst_i)
        1'b1 |=> (adc_dat_b_o[13] == $past(adc_dat_b_i[13]))
    );

    // Channel B lower bits are inverted from the sampled input.
    check_adc_dat_b_low_bits_inverted: assert property (
        @(posedge adc_clk) disable iff (!adc_rst_i)
        1'b1 |=> (adc_dat_b_o[12:0] == ~$past(adc_dat_b_i[12:0]))
    );

endmodule