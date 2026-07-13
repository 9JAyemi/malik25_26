module shift_register_and_counter_sva (
    input logic clk,
    input logic reset,
    input logic [7:0] d,
    input logic [7:0] q_reg,
    input logic [2:0] q_count,
    input logic [7:0] final_output
);

    // Reset clears the registered outputs and final_output on the next cycle.
    check_reset_clears_outputs: assert property (
        @(posedge clk) reset |=> (q_reg == 8'b0) && (q_count == 3'b0) && (final_output == 8'b0)
    );

    // q_reg takes the current d value on each non-reset clock.
    check_q_reg_captures_d: assert property (
        @(posedge clk) disable iff (reset) 1'b1 |=> (q_reg == $past(d))
    );

    // q_count adds d[2:0] modulo 8 on each non-reset clock.
    check_q_count_accumulates_low_bits: assert property (
        @(posedge clk) disable iff (reset) 1'b1 |=> (q_count == $past(q_count + d[2:0]))
    );

    // q_count holds when the low three bits of d are zero.
    check_q_count_holds_on_zero_addend: assert property (
        @(posedge clk) disable iff (reset) (d[2:0] == 3'b000) |=> (q_count == $past(q_count))
    );

    // q_count wraps from 7 to 0 when adding 1.
    check_q_count_wraps_on_overflow: assert property (
        @(posedge clk) disable iff (reset) (q_count == 3'b111 && d[2:0] == 3'b001) |=> (q_count == 3'b000)
    );

    // final_output matches q_reg masked by the zero-extended q_count.
    check_final_output_mask_relation: assert property (
        @(posedge clk) disable iff (reset) (final_output == (q_reg & {5'b0, q_count}))
    );

    // final_output upper five bits are always zero.
    check_final_output_upper_bits_zero: assert property (
        @(posedge clk) disable iff (reset) (final_output[7:3] == 5'b0)
    );

endmodule