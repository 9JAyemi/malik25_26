module adc_fifo_sva (
    input logic        clk,
    input logic [31:0] control,
    input logic [31:0] status,
    input logic        src_adc_enable,
    input logic        src_adc_valid,
    input logic [15:0] src_adc_data,
    input logic        dst_adc_enable,
    input logic        dst_adc_valid,
    input logic [15:0] dst_adc_data
);

    localparam [7:0] RP_ID = 8'hA0;

    // Status is the constant RP_ID value with zeroed upper bits.
    check_status_constant: assert property (
        @(posedge clk) status == {24'h0, RP_ID}
    );

    // Destination enable is the registered copy of source enable from the prior cycle.
    check_enable_pipeline: assert property (
        @(posedge clk) 1'b1 |=> (dst_adc_enable == $past(src_adc_enable))
    );

    // Destination valid is the registered copy of source valid from the prior cycle.
    check_valid_pipeline: assert property (
        @(posedge clk) 1'b1 |=> (dst_adc_valid == $past(src_adc_valid))
    );

    // Destination data is the registered copy of source data from the prior cycle.
    check_data_pipeline: assert property (
        @(posedge clk) 1'b1 |=> (dst_adc_data == $past(src_adc_data))
    );

endmodule