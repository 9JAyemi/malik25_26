module little_endian_counter_assertions (
    input logic clk,
    input logic [3:0] data_in,
    input logic [3:0] data_out
);

    // A max input wraps the registered output to zero on the next cycle.
    check_wrap_from_max: assert property (
        @(posedge clk) (data_in == 4'b1111) |=> (data_out == 4'b0000)
    );

    // A non-max input increments by one on the next cycle.
    check_increment_from_nonmax: assert property (
        @(posedge clk) (data_in != 4'b1111) |=> (data_out == ($past(data_in) + 4'b0001))
    );

    // The output always matches the previous cycle's input transform.
    check_output_matches_previous_input: assert property (
        @(posedge clk) 1'b1 |=> (data_out == (($past(data_in) == 4'b1111) ? 4'b0000 : ($past(data_in) + 4'b0001)))
    );

    // The output is zero exactly when the previous input was 4'hf.
    check_zero_output_only_after_max: assert property (
        @(posedge clk) 1'b1 |=> ((data_out == 4'b0000) == ($past(data_in) == 4'b1111))
    );

endmodule