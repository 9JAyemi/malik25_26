module twos_complement_sva (
    input logic clk,
    input logic [3:0] binary_in,
    input logic [3:0] twos_comp_out
);
    // Output equals bitwise NOT of input plus 1 (two's complement).
    check_twos_comp_equation: assert property (
        @(posedge clk) twos_comp_out == ((~binary_in) + 4'd1)
    );

    // Input plus output wraps to zero (mod 16).
    check_sum_zero_mod16: assert property (
        @(posedge clk) (binary_in + twos_comp_out) == 4'd0
    );

    // Input zero maps to output zero.
    check_zero_in_to_zero_out: assert property (
        @(posedge clk) (binary_in == 4'd0) |-> (twos_comp_out == 4'd0)
    );

    // Output zero implies input zero.
    check_zero_out_implies_zero_in: assert property (
        @(posedge clk) (twos_comp_out == 4'd0) |-> (binary_in == 4'd0)
    );

    // -8 (1000) is a fixed point of two's complement.
    check_neg_eight_fixed_point: assert property (
        @(posedge clk) (binary_in == 4'd8) |-> (twos_comp_out == 4'd8)
    );

    // LSB is preserved by two's complement.
    check_lsb_preserved: assert property (
        @(posedge clk) (twos_comp_out[0] == binary_in[0])
    );

    // Two's complement is involutive: applying it again returns input.
    check_involution: assert property (
        @(posedge clk) ((~twos_comp_out) + 4'd1) == binary_in
    );

    // If input is stable, output is stable next cycle.
    check_output_stable_when_input_stable: assert property (
        @(posedge clk) $stable(binary_in) |=> $stable(twos_comp_out)
    );

    // If input changes between cycles, output changes in the same step.
    check_output_changes_when_input_changes: assert property (
        @(posedge clk) (!$stable(binary_in)) |-> (!$stable(twos_comp_out))
    );

    // Output equals input only for 0 or 8.
    check_equality_only_for_fixed_points: assert property (
        @(posedge clk) (twos_comp_out == binary_in) |-> ((binary_in == 4'd0) || (binary_in == 4'd8))
    );
endmodule