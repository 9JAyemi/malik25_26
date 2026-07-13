module shift_register_sva (
    input logic clk,
    input logic reset,            // Synchronous active-high reset
    input logic [7:0] in,         // DUT port
    input logic [7:0] out,        // DUT port
    input logic [7:0] reg_out,    // DUT port
    input logic [7:0] shift_reg   // Internal reg from DUT
);
    ///// Barrel shifter combinational behavior /////
    // reg_out is left-shifted in with zero-fill LSB.
    check_reg_out_equals_shifted_in: assert property (
        @(posedge clk) disable iff (reset) reg_out == {in[6:0], 1'b0}
    );
    // LSB of reg_out is always 0.
    check_reg_out_lsb_is_zero: assert property (
        @(posedge clk) disable iff (reset) reg_out[0] == 1'b0
    );
    // Upper 7 bits of reg_out mirror lower 7 bits of in.
    check_reg_out_upper_bits_map: assert property (
        @(posedge clk) disable iff (reset) reg_out[7:1] == in[6:0]
    );

    ///// XOR datapath /////
    // out is XOR of in and shift_reg.
    check_out_is_xor_of_inputs: assert property (
        @(posedge clk) disable iff (reset) out == (in ^ shift_reg)
    );

    ///// Sequential shift_reg update /////
    // On the next cycle (no reset), shift_reg captures current reg_out.
    check_shift_reg_captures_reg_out_next_cycle: assert property (
        @(posedge clk) disable iff (reset) 1'b1 |-> ##1 (shift_reg == $past(reg_out))
    );
    // On the next cycle after reset is asserted, shift_reg becomes 0.
    check_reset_clears_shift_reg_next_cycle: assert property (
        @(posedge clk) reset |=> (shift_reg == 8'h00)
    );
    // On the next cycle after reset is asserted, out equals in (since shift_reg=0).
    check_out_equals_in_one_cycle_after_reset: assert property (
        @(posedge clk) reset |=> (out == in)
    );
    // While reset remains asserted, shift_reg stays 0.
    check_shift_reg_stays_zero_while_reset: assert property (
        @(posedge clk) (reset && $past(reset)) |-> (shift_reg == 8'h00)
    );

    ///// Derived sequential relationships /////
    // On the next cycle (no reset), shift_reg equals previous shifted in.
    check_shift_reg_captures_shifted_in_next_cycle: assert property (
        @(posedge clk) disable iff (reset) 1'b1 |-> ##1 (shift_reg == $past({in[6:0], 1'b0}))
    );
    // On the next cycle (no reset), out equals current in XOR previous shifted in.
    check_pipeline_out_uses_prev_shifted_in: assert property (
        @(posedge clk) disable iff (reset) 1'b1 |-> ##1 (out == (in ^ $past({in[6:0], 1'b0})))
    );

    ///// Simple stability check /////
    // If in is stable across cycles (no reset), reg_out is stable.
    check_reg_out_stable_when_in_stable: assert property (
        @(posedge clk) disable iff (reset) $stable(in) |-> $stable(reg_out)
    );
endmodule