module accumulator_assertions (
    input logic        clk,
    input logic [7:0]  data_in,
    input logic [31:0] sum_out
);

    // sum_out accumulates the previous cycle's data_in every clock.
    check_sum_accumulates: assert property (
        @(posedge clk) disable iff (1'b0)
        1'b1 |=> (sum_out == ($past(sum_out) + $past(data_in)))
    );

    // A zero input leaves sum_out unchanged on the next clock.
    check_zero_input_holds: assert property (
        @(posedge clk) disable iff (1'b0)
        1'b1 |=> (($past(data_in) == 8'h00) -> (sum_out == $past(sum_out)))
    );

    // The low byte updates as the previous low byte plus previous data_in.
    check_low_byte_updates: assert property (
        @(posedge clk) disable iff (1'b0)
        1'b1 |=> (sum_out[7:0] == ($past(sum_out[7:0]) + $past(data_in)))
    );

    // Without a low-byte carry, the upper 24 bits stay unchanged.
    check_no_low_byte_carry_keeps_upper: assert property (
        @(posedge clk) disable iff (1'b0)
        1'b1 |=> ((({1'b0, $past(sum_out[7:0])} + {1'b0, $past(data_in)}) < 9'h100) ->
                  (sum_out[31:8] == $past(sum_out[31:8])))
    );

    // A low-byte carry increments the upper 24 bits by one.
    check_low_byte_carry_increments_upper: assert property (
        @(posedge clk) disable iff (1'b0)
        1'b1 |=> ((({1'b0, $past(sum_out[7:0])} + {1'b0, $past(data_in)}) >= 9'h100) ->
                  (sum_out[31:8] == ($past(sum_out[31:8]) + 24'd1)))
    );

endmodule