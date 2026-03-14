module top_module_sva (
    input logic clk,
    input logic reset,
    input logic data,
    input logic q,
    input logic [2:0] shift_reg_out,
    input logic d_ff_out
);
    // q must be XOR of shift_reg_out[2] and d_ff_out.
    check_output_is_xor: assert property (
        @(posedge clk) disable iff (reset) q == (shift_reg_out[2] ^ d_ff_out)
    );

    // d_ff_out samples shift_reg_out[2] each cycle when not in reset.
    check_dff_samples_sr2: assert property (
        @(posedge clk) disable iff (reset) d_ff_out == $past(shift_reg_out[2])
    );

    // shift_reg_out[2] advances from prior shift_reg_out[1].
    check_shift_sr2_advances: assert property (
        @(posedge clk) disable iff (reset) shift_reg_out[2] == $past(shift_reg_out[1])
    );

    // shift_reg_out[1] advances from prior shift_reg_out[0].
    check_shift_sr1_advances: assert property (
        @(posedge clk) disable iff (reset) shift_reg_out[1] == $past(shift_reg_out[0])
    );

    // shift_reg_out[0] captures prior data.
    check_shift_sr0_captures_data: assert property (
        @(posedge clk) disable iff (reset) shift_reg_out[0] == $past(data)
    );

    // q equals current XOR previous value of shift_reg_out[2].
    check_q_equals_sr2_xor_past: assert property (
        @(posedge clk) disable iff (reset) q == (shift_reg_out[2] ^ $past(shift_reg_out[2]))
    );

    // If shift_reg_out[2] is stable across cycles, q must be 0.
    check_q_zero_if_sr2_stable: assert property (
        @(posedge clk) disable iff (reset) (shift_reg_out[2] == $past(shift_reg_out[2])) |-> (q == 1'b0)
    );

    // On a rising edge of shift_reg_out[2], q must be 1.
    check_q_one_on_sr2_rise: assert property (
        @(posedge clk) disable iff (reset) $rose(shift_reg_out[2]) |-> (q == 1'b1)
    );

    // On a falling edge of shift_reg_out[2], q must be 1.
    check_q_one_on_sr2_fall: assert property (
        @(posedge clk) disable iff (reset) $fell(shift_reg_out[2]) |-> (q == 1'b1)
    );

    // Immediately after reset deasserts, shift_reg_out must be {0,0,$past(data)}.
    check_shift_init_after_reset_release: assert property (
        @(posedge clk) disable iff (reset) ($past(reset) && !reset) |-> (shift_reg_out == {2'b00, $past(data)})
    );

    // Immediately after reset deasserts, d_ff_out must be 0.
    check_dff_zero_after_reset_release: assert property (
        @(posedge clk) disable iff (reset) ($past(reset) && !reset) |-> (d_ff_out == 1'b0)
    );
endmodule