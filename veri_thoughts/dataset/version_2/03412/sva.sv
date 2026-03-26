module shift_and_zero_sva (
    input logic       clk,
    input logic [3:0] in,
    input logic       rst,
    input logic [3:0] out
);

    // Reset forces the output to zero.
    check_reset_zero: assert property (
        @(posedge clk) rst |-> (out == 4'b0000)
    );

    // Outside reset, output is the upper two input bits followed by zeros.
    check_shift_mapping: assert property (
        @(posedge clk) disable iff (rst)
            (out == {in[3:2], 2'b00})
    );

    // The low two output bits are always zero.
    check_low_bits_zero: assert property (
        @(posedge clk) (out[1:0] == 2'b00)
    );

    // Outside reset, the high two output bits mirror the high input bits.
    check_upper_bits_match: assert property (
        @(posedge clk) disable iff (rst)
            (out[3:2] == in[3:2])
    );

    // With reset low across samples, stable input keeps the output stable.
    check_stable_input_stable_output: assert property (
        @(posedge clk) disable iff (rst)
            (!$past(rst) && $stable(in)) |-> $stable(out)
    );

    // With reset low across samples, changing only in[1:0] does not change out.
    check_lower_input_bits_ignored: assert property (
        @(posedge clk) disable iff (rst)
            (!$past(rst) &&
             (in[3:2] == $past(in[3:2])) &&
             (in[1:0] != $past(in[1:0]))) |-> (out == $past(out))
    );

endmodule