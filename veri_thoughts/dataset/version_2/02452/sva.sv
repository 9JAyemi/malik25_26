module top_module_sva (
    input logic CLK,
    input logic [15:0] in,
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [7:0] out
);
    // out equals lower 8 bits of (high_byte(a*b) + low_byte(a*b))
    check_out_is_byte_sum_of_ab_product: assert property (
        @(posedge CLK) out == (((a*b)[15:8] + (a*b)[7:0]) [7:0])
    );

    // If either multiplier input is zero, output must be zero
    check_zero_input_results_zero_output: assert property (
        @(posedge CLK) ((a == 8'h00) || (b == 8'h00)) |-> (out == 8'h00)
    );

    // If a is 1, output equals b
    check_a_one_passthrough_b: assert property (
        @(posedge CLK) (a == 8'h01) |-> (out == b)
    );

    // If b is 1, output equals a
    check_b_one_passthrough_a: assert property (
        @(posedge CLK) (b == 8'h01) |-> (out == a)
    );

    // If high byte of a*b is zero, output equals low byte of a*b
    check_hi_byte_zero_then_out_eq_low_byte: assert property (
        @(posedge CLK) (((a*b)[15:8]) == 8'h00) |-> (out == (a*b)[7:0])
    );

    // If low byte of a*b is zero, output equals high byte of a*b
    check_lo_byte_zero_then_out_eq_high_byte: assert property (
        @(posedge CLK) (((a*b)[7:0]) == 8'h00) |-> (out == (a*b)[15:8])
    );

    // If a and b are stable, out must be stable (pure combinational behavior)
    check_output_stable_when_a_b_stable: assert property (
        @(posedge CLK) ($stable(a) && $stable(b)) |-> $stable(out)
    );

    // Swapping a and b across consecutive cycles preserves out due to commutativity
    check_swap_a_b_preserves_out_next_cycle: assert property (
        @(posedge CLK) ((a == $past(b)) && (b == $past(a))) |-> (out == $past(out))
    );

    // Toggling unused input 'in' does not affect out when a and b are stable
    check_out_independent_of_in_toggle: assert property (
        @(posedge CLK) ($changed(in) && $stable(a) && $stable(b)) |-> $stable(out)
    );

    // For a = 0xFF and b = 0xFF, output is 0xFF (0xFE + 0x01)
    check_all_ones_mult_results_ff_out: assert property (
        @(posedge CLK) ((a == 8'hFF) && (b == 8'hFF)) |-> (out == 8'hFF)
    );
endmodule