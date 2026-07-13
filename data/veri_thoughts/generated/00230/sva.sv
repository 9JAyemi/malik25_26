module ad_datafmt_sva #(
    parameter DATA_WIDTH = 16,
    parameter DISABLE = 0
) (
    input logic clk,
    input logic valid,
    input logic [(DATA_WIDTH-1):0] data,
    input logic valid_out,
    input logic [15:0] data_out,
    input logic dfmt_enable,
    input logic dfmt_type,
    input logic dfmt_se
);

generate
if (DISABLE == 1) begin : g_disabled

    // valid_out directly mirrors valid when the block is disabled.
    check_disabled_valid_passthrough: assert property (
        @(posedge clk) valid_out == valid
    );

    if (DATA_WIDTH < 16) begin : g_disabled_narrow

        // data_out is a zero-extended copy of data when the block is disabled.
        check_disabled_data_zero_extend: assert property (
            @(posedge clk) data_out == {{(16-DATA_WIDTH){1'b0}}, data}
        );

        // Upper output bits stay zero for narrow disabled configurations.
        check_disabled_upper_zero: assert property (
            @(posedge clk) data_out[15:DATA_WIDTH] == {(16-DATA_WIDTH){1'b0}}
        );

    end else begin : g_disabled_wide

        // data_out directly mirrors the low 16 bits of data when disabled.
        check_disabled_data_word_copy: assert property (
            @(posedge clk) data_out == data[15:0]
        );

    end

end else begin : g_enabled

    // valid_out is the registered valid input.
    check_enabled_valid_pipeline: assert property (
        @(posedge clk) 1'b1 |=> (valid_out == $past(valid))
    );

    if (DATA_WIDTH > 1) begin : g_enabled_low_bits

        // Lower data bits are registered without modification.
        check_enabled_lower_bits_pipeline: assert property (
            @(posedge clk) 1'b1 |=> (data_out[DATA_WIDTH-2:0] == $past(data[DATA_WIDTH-2:0]))
        );

    end

    // The output sign bit is optionally inverted and then registered.
    check_enabled_sign_bit_format: assert property (
        @(posedge clk) 1'b1 |=> (data_out[DATA_WIDTH-1] == ($past(dfmt_enable & dfmt_type) ^ $past(data[DATA_WIDTH-1])))
    );

    // With dfmt_type inactive, the sign bit is preserved.
    check_enabled_type_zero_preserve_sign: assert property (
        @(posedge clk) 1'b1 |=> ($past(dfmt_enable & dfmt_type) || (data_out[DATA_WIDTH-1] == $past(data[DATA_WIDTH-1])))
    );

    // With dfmt_type active, the sign bit is inverted.
    check_enabled_type_one_invert_sign: assert property (
        @(posedge clk) 1'b1 |=> (!$past(dfmt_enable & dfmt_type) || (data_out[DATA_WIDTH-1] == ~$past(data[DATA_WIDTH-1])))
    );

    if (DATA_WIDTH < 16) begin : g_enabled_narrow

        // Upper bits clear when sign extension was not enabled.
        check_enabled_upper_zero_without_signext: assert property (
            @(posedge clk) 1'b1 |=> ($past(dfmt_enable & dfmt_se) || (data_out[15:DATA_WIDTH] == {(16-DATA_WIDTH){1'b0}}))
        );

        // Upper bits replicate the formatted sign bit when sign extension is enabled.
        check_enabled_upper_signext: assert property (
            @(posedge clk) 1'b1 |=> (!$past(dfmt_enable & dfmt_se) || (data_out[15:DATA_WIDTH] == {(16-DATA_WIDTH){data_out[DATA_WIDTH-1]}}))
        );

        // dfmt_enable low produces a zero-extended registered copy of data.
        check_enabled_dfmt_disable_zero_extend: assert property (
            @(posedge clk) 1'b1 |=> ($past(dfmt_enable) || (data_out == {{(16-DATA_WIDTH){1'b0}}, $past(data)}))
        );

    end else begin : g_enabled_wide

        // dfmt_enable low produces a registered copy of data.
        check_enabled_dfmt_disable_word_copy: assert property (
            @(posedge clk) 1'b1 |=> ($past(dfmt_enable) || (data_out == $past(data[15:0])))
        );

    end

end
endgenerate

endmodule