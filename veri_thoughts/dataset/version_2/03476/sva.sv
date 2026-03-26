module axis_red_pitaya_adc_sva #(
    parameter integer ADC_DATA_WIDTH   = 14,
    parameter integer AXIS_TDATA_WIDTH = 32
) (
    input logic                        aclk,
    input logic                        adc_csn,
    input logic [ADC_DATA_WIDTH-1:0]   adc_dat_a,
    input logic [ADC_DATA_WIDTH-1:0]   adc_dat_b,
    input logic                        m_axis_tvalid,
    input logic [AXIS_TDATA_WIDTH-1:0] m_axis_tdata
);

    localparam integer PADDING_WIDTH = AXIS_TDATA_WIDTH/2 - ADC_DATA_WIDTH;
    localparam integer HALF_WIDTH    = AXIS_TDATA_WIDTH/2;

    // adc_csn is tied high.
    check_adc_csn_high: assert property (
        @(posedge aclk) adc_csn == 1'b1
    );

    // m_axis_tvalid is tied high.
    check_m_axis_tvalid_high: assert property (
        @(posedge aclk) m_axis_tvalid == 1'b1
    );

    // Upper AXIS half encodes the previous adc_dat_b sample.
    check_tdata_upper_half_from_prev_b: assert property (
        @(posedge aclk)
        !$initstate |-> m_axis_tdata[AXIS_TDATA_WIDTH-1:HALF_WIDTH] ==
                        {{(PADDING_WIDTH+1){$past(adc_dat_b[ADC_DATA_WIDTH-1])}},
                         ~($past(adc_dat_b[ADC_DATA_WIDTH-2:0]))}
    );

    // Lower AXIS half encodes the previous adc_dat_a sample.
    check_tdata_lower_half_from_prev_a: assert property (
        @(posedge aclk)
        !$initstate |-> m_axis_tdata[HALF_WIDTH-1:0] ==
                        {{(PADDING_WIDTH+1){$past(adc_dat_a[ADC_DATA_WIDTH-1])}},
                         ~($past(adc_dat_a[ADC_DATA_WIDTH-2:0]))}
    );

    // Upper sign bits replicate the previous adc_dat_b sign bit.
    check_upper_sign_extension_from_prev_b: assert property (
        @(posedge aclk)
        !$initstate |-> m_axis_tdata[AXIS_TDATA_WIDTH-1:HALF_WIDTH+ADC_DATA_WIDTH-1] ==
                        {(PADDING_WIDTH+1){$past(adc_dat_b[ADC_DATA_WIDTH-1])}}
    );

    // Upper payload bits invert the previous adc_dat_b lower bits.
    check_upper_payload_inverted_from_prev_b: assert property (
        @(posedge aclk)
        !$initstate |-> m_axis_tdata[HALF_WIDTH+ADC_DATA_WIDTH-2:HALF_WIDTH] ==
                        ~($past(adc_dat_b[ADC_DATA_WIDTH-2:0]))
    );

    // Lower sign bits replicate the previous adc_dat_a sign bit.
    check_lower_sign_extension_from_prev_a: assert property (
        @(posedge aclk)
        !$initstate |-> m_axis_tdata[HALF_WIDTH-1:ADC_DATA_WIDTH-1] ==
                        {(PADDING_WIDTH+1){$past(adc_dat_a[ADC_DATA_WIDTH-1])}}
    );

    // Lower payload bits invert the previous adc_dat_a lower bits.
    check_lower_payload_inverted_from_prev_a: assert property (
        @(posedge aclk)
        !$initstate |-> m_axis_tdata[ADC_DATA_WIDTH-2:0] ==
                        ~($past(adc_dat_a[ADC_DATA_WIDTH-2:0]))
    );

endmodule