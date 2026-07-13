module cf_jesd_align_2_sva (
    input logic        rx_clk,
    input logic [3:0]  rx_sof,
    input logic [3:0]  rx_eof,
    input logic [3:0]  rx_ferr,
    input logic [31:0] rx_fdata,
    input logic        rx_err,
    input logic [31:0] rx_data
);

    // SOF 0101 passes the prior cycle input word through and updates rx_err from eof/ferr.
    check_sof_0101_outputs: assert property (
        @(posedge rx_clk)
        ($past(1'b1) && ($past(rx_sof) == 4'b0101)) |->
            ((rx_err == !(($past(rx_sof) == ~$past(rx_eof)) && ($past(rx_ferr) == 4'd0))) &&
             (rx_data == $past(rx_fdata)))
    );

    // SOF 1010 uses the prior word's low 24 bits and the earlier word's top byte.
    check_sof_1010_outputs: assert property (
        @(posedge rx_clk)
        ($past(1'b1, 2) && ($past(rx_sof) == 4'b1010)) |->
            ((rx_err == !(($past(rx_sof) == ~$past(rx_eof)) && ($past(rx_ferr) == 4'd0))) &&
             (rx_data == {$past(rx_fdata[23:0]), $past(rx_fdata[31:24], 2)}))
    );

    // Any non-0101/non-1010 SOF drives the default error and data pattern.
    check_invalid_sof_outputs: assert property (
        @(posedge rx_clk)
        ($past(1'b1) && ($past(rx_sof) != 4'b0101) && ($past(rx_sof) != 4'b1010)) |->
            ((rx_err == 1'b1) &&
             (rx_data == 32'hffff))
    );

    // A clean valid SOF with matching inverted EOF clears rx_err.
    check_clean_valid_frame_clears_error: assert property (
        @(posedge rx_clk)
        ($past(1'b1) &&
         (($past(rx_sof) == 4'b0101) || ($past(rx_sof) == 4'b1010)) &&
         ($past(rx_sof) == ~$past(rx_eof)) &&
         ($past(rx_ferr) == 4'd0)) |->
            (rx_err == 1'b0)
    );

    // A valid SOF with EOF mismatch or frame error sets rx_err.
    check_bad_valid_frame_sets_error: assert property (
        @(posedge rx_clk)
        ($past(1'b1) &&
         (($past(rx_sof) == 4'b0101) || ($past(rx_sof) == 4'b1010)) &&
         (($past(rx_sof) != ~$past(rx_eof)) || ($past(rx_ferr) != 4'd0))) |->
            (rx_err == 1'b1)
    );

    // rx_err low can only result from a clean valid SOF on the prior cycle.
    check_error_low_has_clean_valid_cause: assert property (
        @(posedge rx_clk)
        ($past(1'b1) && (rx_err == 1'b0)) |->
            ((($past(rx_sof) == 4'b0101) || ($past(rx_sof) == 4'b1010)) &&
             ($past(rx_sof) == ~$past(rx_eof)) &&
             ($past(rx_ferr) == 4'd0))
    );

endmodule