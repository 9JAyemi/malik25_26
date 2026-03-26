module shift_reg_sva(
    input logic       in,
    input logic       shift,
    input logic       clk,
    input logic       reset,
    input logic [3:0] out
);

    // Active-low reset clears the register.
    check_reset_clears_out: assert property (
        @(posedge clk) disable iff ($initstate)
        !reset |-> (out == 4'b0)
    );

    // When shift is high, bits [2:0] move into [3:1] on the next clock.
    check_shift_moves_upper_bits: assert property (
        @(posedge clk) disable iff (!reset || $initstate)
        shift |=> (out[3:1] == $past(out[2:0]))
    );

    // When shift is high, the input is captured into bit 0 on the next clock.
    check_shift_loads_input_bit: assert property (
        @(posedge clk) disable iff (!reset || $initstate)
        shift |=> (out[0] == $past(in))
    );

    // When shift is low, the register holds its previous value.
    check_hold_when_shift_low: assert property (
        @(posedge clk) disable iff (!reset || $initstate)
        !shift |=> (out == $past(out))
    );

endmodule