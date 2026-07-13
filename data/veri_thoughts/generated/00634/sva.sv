module top_module_sva (
    input logic clk,
    input logic reset,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic serial_in,
    input logic shift,
    input logic [3:0] parallel_out,
    input logic final_output
);
    // Reset drives parallel_out to zero.
    reset_clears_parallel_out: assert property (
        @(posedge clk) reset |-> (parallel_out == 4'b0000)
    );

    // On shift, next parallel_out equals {prev serial_in, prev parallel_out[3:1]}.
    shift_loads_next_value: assert property (
        @(posedge clk) disable iff (reset) (!$initstate && shift) |=> (parallel_out == { $past(serial_in), $past(parallel_out)[3:1] })
    );

    // Without shift, parallel_out holds its previous value.
    hold_without_shift: assert property (
        @(posedge clk) disable iff (reset) (!$initstate && !shift) |=> (parallel_out == $past(parallel_out))
    );

    // On shift, MSB becomes the previous serial_in.
    shift_msb_inserts_serial_in: assert property (
        @(posedge clk) disable iff (reset) (!$initstate && shift) |=> (parallel_out[3] == $past(serial_in))
    );

    // On shift, lower bits shift right by one.
    shift_lower_bits_move_right: assert property (
        @(posedge clk) disable iff (reset) (!$initstate && shift) |=> (parallel_out[2:0] == $past(parallel_out[3:1]))
    );

    // After reset deasserts, if no shift occurs, parallel_out remains zero.
    retain_zero_after_reset_no_shift: assert property (
        @(posedge clk) disable iff (reset) (!$initstate && !reset && $past(reset) && !shift) |-> (parallel_out == 4'b0000)
    );

    // final_output matches combinational logic: (A==B || A>B || A<B) && (parallel_out != 0).
    final_output_matches_logic: assert property (
        @(posedge clk) disable iff (reset) final_output == (((A==B) || (A>B) || (A<B)) && (parallel_out != 4'b0000))
    );

    // final_output must be 0 when parallel_out is zero.
    final_output_zero_when_parallel_zero: assert property (
        @(posedge clk) disable iff (reset) (parallel_out == 4'b0000) |-> (final_output == 1'b0)
    );

    // final_output == 1 requires parallel_out != 0 and one of the relations to hold.
    final_output_one_requires_nonzero_parallel: assert property (
        @(posedge clk) disable iff (reset) (final_output == 1'b1) |-> ((parallel_out != 4'b0000) && ((A==B) || (A>B) || (A<B)))
    );
endmodule