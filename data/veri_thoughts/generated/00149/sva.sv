module subtractor_sva (
    input logic [8:0] count_d2_reg,
    input logic [3:0] S,
    input logic wr_clk,
    input logic AR,
    input logic [9:0] wr_data_count
);

    wire [3:0] constant_value;
    assign constant_value = 4'd10 - (S * 10);

    wire [8:0] subtracted_value;
    assign subtracted_value = count_d2_reg - constant_value;

    // A sampled active-low reset leaves the output at zero on the next clock sample.
    check_reset_drives_zero_next_sample: assert property (
        @(posedge wr_clk) !AR |=> (wr_data_count == 10'd0)
    );

    // The low 9 bits register the prior subtraction result when reset stays deasserted.
    check_registered_lower_bits: assert property (
        @(posedge wr_clk) disable iff (!AR)
        1'b1 |=> (wr_data_count[8:0] == $past(subtracted_value))
    );

    // The registered output always loads with a zero in the top bit.
    check_zero_extended_msb: assert property (
        @(posedge wr_clk) disable iff (!AR)
        1'b1 |=> (wr_data_count[9] == 1'b0)
    );

    // A subtraction result of zero is loaded as an all-zero output.
    check_zero_result_loads_zero: assert property (
        @(posedge wr_clk) disable iff (!AR)
        (subtracted_value == 9'd0) |=> (wr_data_count == 10'd0)
    );

    // A high subtraction MSB is carried in bit 8 only, not sign-extended into bit 9.
    check_no_sign_extension: assert property (
        @(posedge wr_clk) disable iff (!AR)
        subtracted_value[8] |=> ((wr_data_count[9] == 1'b0) && (wr_data_count[8] == 1'b1))
    );

endmodule