module four_bit_adder_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic mode,
    input logic reset,
    input logic carry_in,
    input logic CLK,
    input logic [3:0] C,
    input logic carry_out
);

    // Reset clears the registered output on the following clock.
    check_reset_clears_c: assert property (
        @(posedge CLK) reset |=> (C == 4'b0000)
    );

    // carry_out matches the MSB of the current 5-bit addition.
    check_carry_out_matches_addition: assert property (
        @(posedge CLK) disable iff (reset)
            carry_out == (({carry_in, A} + {mode, B})[4])
    );

    // C captures the low 4 bits of the previous cycle's addition.
    check_c_registers_sum_low_bits: assert property (
        @(posedge CLK) disable iff (reset)
            1'b1 |=> ({1'b0, C} == ($past({carry_in, A} + {mode, B}) & 5'h0F))
    );

    // With held inputs across non-reset cycles, sampled outputs match the current addition.
    check_outputs_match_addition_when_inputs_hold: assert property (
        @(posedge CLK) disable iff (reset)
            (!$past(reset) && $stable({A, B, mode, carry_in})) |-> ({carry_out, C} == ({carry_in, A} + {mode, B}))
    );

endmodule