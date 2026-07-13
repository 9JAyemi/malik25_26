module top_module_sva (
    input logic clk,
    input logic reset, // Synchronous active-high reset
    input logic [7:0] in_data,
    input logic out_signal,

    // Internal signals from DUT (bind to these by name)
    input logic [7:0] shift_reg,
    input logic parity,
    input logic d_ff,
    input logic xor_output
);

    ///// Reset behavior /////
    // On reset, shift_reg is cleared to 0 by the next clock.
    check_reset_clears_shift_reg: assert property (
        @(posedge clk) reset |=> (shift_reg == 8'h00)
    );

    // On reset, d_ff is cleared to 0 by the next clock.
    check_reset_clears_dff: assert property (
        @(posedge clk) reset |=> (d_ff == 1'b0)
    );

    // On reset, out_signal is cleared to 0 by the next clock.
    check_reset_clears_out: assert property (
        @(posedge clk) reset |=> (out_signal == 1'b0)
    );

    ///// Combinational definitions /////
    // Parity equals reduction XOR of in_data when not in reset.
    check_parity_definition: assert property (
        @(posedge clk) disable iff (reset) (parity == ^in_data)
    );

    // xor_output equals parity XOR d_ff when not in reset.
    check_xor_output_definition: assert property (
        @(posedge clk) disable iff (reset) (xor_output == (parity ^ d_ff))
    );

    ///// Sequential updates /////
    // d_ff captures in_data[0] from the previous cycle (when previous cycle not in reset).
    check_dff_captures_in_lsb: assert property (
        @(posedge clk) disable iff (reset) (!$past(reset)) |-> (d_ff == $past(in_data[0]))
    );

    // shift_reg shifts left and appends parity from the previous cycle (when previous cycle not in reset).
    check_shift_reg_shifts_with_parity: assert property (
        @(posedge clk) disable iff (reset) (!$past(reset)) |-> (shift_reg == { $past(shift_reg[6:0]), $past(parity) })
    );

    // shift_reg[7] moves from previous shift_reg[6] (when previous cycle not in reset).
    check_shift_reg_msb_moves_from_bit6: assert property (
        @(posedge clk) disable iff (reset) (!$past(reset)) |-> (shift_reg[7] == $past(shift_reg[6]))
    );

    // out_signal equals previous cycle's shift_reg[7] (when previous cycle not in reset).
    check_out_signal_follows_shift_msb: assert property (
        @(posedge clk) disable iff (reset) (!$past(reset)) |-> (out_signal == $past(shift_reg[7]))
    );

endmodule