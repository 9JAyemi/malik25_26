module top_module_sva (
    input logic       clk,
    input logic       reset,
    input logic       a,
    input logic       b,
    input logic       out,
    input logic [7:0] shift_reg
);

    // Reset loads the shift register with 8'h34.
    check_reset_loads_shift_reg: assert property (
        @(posedge clk) reset |=> (shift_reg == 8'h34)
    );

    // A non-reset cycle shifts left and loads a into bit 0.
    check_shift_reg_updates: assert property (
        @(posedge clk) disable iff (reset)
        (!$initstate && !$past(reset)) |-> (shift_reg == {$past(shift_reg[6:0]), $past(a)})
    );

    // out is the truncated LSB of shift_reg & (a ^ b).
    check_out_matches_truncated_and: assert property (
        @(posedge clk) disable iff (reset)
        out == (shift_reg[0] & (a ^ b))
    );

    // Equal inputs make the XOR term low, so out must be low.
    check_out_low_when_inputs_equal: assert property (
        @(posedge clk) disable iff (reset)
        (a == b) |-> (out == 1'b0)
    );

    // out can only be high when the XOR term is high.
    check_out_requires_xor_high: assert property (
        @(posedge clk) disable iff (reset)
        out |-> (a ^ b)
    );

    // out can only be high when shift_reg bit 0 is high.
    check_out_requires_shift_reg_lsb_high: assert property (
        @(posedge clk) disable iff (reset)
        out |-> shift_reg[0]
    );

    // The reset value has bit 0 low, so out is low after reset.
    check_reset_forces_out_low: assert property (
        @(posedge clk) reset |=> (out == 1'b0)
    );

endmodule