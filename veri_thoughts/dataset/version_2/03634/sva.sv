module axi_ad9234_if_sva (
    input logic         rx_clk,
    input logic [127:0] rx_data,
    input logic         adc_clk,
    input logic         adc_rst,
    input logic [63:0]  adc_data_a,
    input logic [63:0]  adc_data_b,
    input logic         adc_or_a,
    input logic         adc_or_b,
    input logic         adc_status
);

    // adc_clk mirrors rx_clk at the sampling edge.
    check_adc_clk_mirrors_rx_clk: assert property (
        @(posedge rx_clk) disable iff (adc_rst)
        (adc_clk == rx_clk)
    );

    // adc_or_a is tied low.
    check_adc_or_a_tied_low: assert property (
        @(posedge rx_clk) disable iff (adc_rst)
        (adc_or_a == 1'b0)
    );

    // adc_or_b is tied low.
    check_adc_or_b_tied_low: assert property (
        @(posedge rx_clk) disable iff (adc_rst)
        (adc_or_b == 1'b0)
    );

    // adc_data_a[63:48] matches the s3 byte mapping.
    check_adc_data_a_s3_mapping: assert property (
        @(posedge rx_clk) disable iff (adc_rst)
        (adc_data_a[63:48] == {rx_data[31:24], rx_data[63:56]})
    );

    // adc_data_a[47:32] matches the s2 byte mapping.
    check_adc_data_a_s2_mapping: assert property (
        @(posedge rx_clk) disable iff (adc_rst)
        (adc_data_a[47:32] == {rx_data[23:16], rx_data[55:48]})
    );

    // adc_data_a[31:16] matches the s1 byte mapping.
    check_adc_data_a_s1_mapping: assert property (
        @(posedge rx_clk) disable iff (adc_rst)
        (adc_data_a[31:16] == {rx_data[15:8], rx_data[47:40]})
    );

    // adc_data_a[15:0] matches the s0 byte mapping.
    check_adc_data_a_s0_mapping: assert property (
        @(posedge rx_clk) disable iff (adc_rst)
        (adc_data_a[15:0] == {rx_data[7:0], rx_data[39:32]})
    );

    // adc_data_b[63:48] matches the s3 byte mapping.
    check_adc_data_b_s3_mapping: assert property (
        @(posedge rx_clk) disable iff (adc_rst)
        (adc_data_b[63:48] == {rx_data[95:88], rx_data[127:120]})
    );

    // adc_data_b[47:32] matches the s2 byte mapping.
    check_adc_data_b_s2_mapping: assert property (
        @(posedge rx_clk) disable iff (adc_rst)
        (adc_data_b[47:32] == {rx_data[87:80], rx_data[119:112]})
    );

    // adc_data_b[31:16] matches the s1 byte mapping.
    check_adc_data_b_s1_mapping: assert property (
        @(posedge rx_clk) disable iff (adc_rst)
        (adc_data_b[31:16] == {rx_data[79:72], rx_data[111:104]})
    );

    // adc_data_b[15:0] matches the s0 byte mapping.
    check_adc_data_b_s0_mapping: assert property (
        @(posedge rx_clk) disable iff (adc_rst)
        (adc_data_b[15:0] == {rx_data[71:64], rx_data[103:96]})
    );

    // adc_status clears one cycle after reset is sampled high.
    check_adc_status_clears_after_reset: assert property (
        @(posedge rx_clk)
        adc_rst |=> (adc_status == 1'b0)
    );

    // adc_status sets one cycle after reset is sampled low.
    check_adc_status_sets_after_nonreset: assert property (
        @(posedge rx_clk)
        !adc_rst |=> (adc_status == 1'b1)
    );

endmodule