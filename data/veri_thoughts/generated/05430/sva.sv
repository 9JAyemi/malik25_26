module final_module_sva(
    input logic        cout_adder,
    input logic [2:0]  sum_adder,
    input logic [2:0]  out_or_bitwise,
    input logic        out_or_logical,
    input logic [5:0]  out_not,
    input logic [5:0]  final_output
);

    // No explicit clock or reset exists in the RTL; this logic is combinational.

    // final_output[0] is the implemented XOR/add result of the bit-0 inputs.
    check_final_output_bit0_function: assert property (
        @($global_clock)
        final_output[0] === (sum_adder[0] ^ out_or_bitwise[0] ^ cout_adder ^ out_not[0])
    );

    // Known bit-0 inputs must produce a known final_output[0].
    check_final_output_bit0_known_when_inputs_known: assert property (
        @($global_clock)
        (!$isunknown({sum_adder[0], out_or_bitwise[0], cout_adder, out_not[0]}))
        |-> (!$isunknown(final_output[0]))
    );

    // With all used inputs stable, the combinational output must stay stable.
    check_used_inputs_stable_keep_output_stable: assert property (
        @($global_clock)
        ($stable(cout_adder) &&
         $stable(sum_adder) &&
         $stable(out_or_bitwise) &&
         $stable(out_not))
        |-> $stable(final_output)
    );

    // final_output[0] depends only on the bit-0 contributors.
    check_output0_depends_only_on_bit0_inputs: assert property (
        @($global_clock)
        ($stable(sum_adder[0]) &&
         $stable(out_or_bitwise[0]) &&
         $stable(cout_adder) &&
         $stable(out_not[0]))
        |-> $stable(final_output[0])
    );

    // out_or_logical is unused and must not affect the output.
    check_out_or_logical_unused: assert property (
        @($global_clock)
        ($changed(out_or_logical) &&
         $stable(cout_adder) &&
         $stable(sum_adder) &&
         $stable(out_or_bitwise) &&
         $stable(out_not))
        |-> $stable(final_output)
    );

    // Toggling sum_adder[0] alone flips final_output[0].
    check_sum_adder0_toggle_flips_output0: assert property (
        @($global_clock)
        ((!$isunknown({$past(sum_adder[0]), sum_adder[0], out_or_bitwise[0], cout_adder, out_not[0]})) &&
         $changed(sum_adder[0]) &&
         $stable(out_or_bitwise[0]) &&
         $stable(cout_adder) &&
         $stable(out_not[0]))
        |-> $changed(final_output[0])
    );

    // Toggling out_or_bitwise[0] alone flips final_output[0].
    check_out_or_bitwise0_toggle_flips_output0: assert property (
        @($global_clock)
        ((!$isunknown({sum_adder[0], $past(out_or_bitwise[0]), out_or_bitwise[0], cout_adder, out_not[0]})) &&
         $stable(sum_adder[0]) &&
         $changed(out_or_bitwise[0]) &&
         $stable(cout_adder) &&
         $stable(out_not[0]))
        |-> $changed(final_output[0])
    );

    // Toggling cout_adder alone flips final_output[0].
    check_cout_adder_toggle_flips_output0: assert property (
        @($global_clock)
        ((!$isunknown({sum_adder[0], out_or_bitwise[0], $past(cout_adder), cout_adder, out_not[0]})) &&
         $stable(sum_adder[0]) &&
         $stable(out_or_bitwise[0]) &&
         $changed(cout_adder) &&
         $stable(out_not[0]))
        |-> $changed(final_output[0])
    );

    // Toggling out_not[0] alone flips final_output[0].
    check_out_not0_toggle_flips_output0: assert property (
        @($global_clock)
        ((!$isunknown({sum_adder[0], out_or_bitwise[0], cout_adder, $past(out_not[0]), out_not[0]})) &&
         $stable(sum_adder[0]) &&
         $stable(out_or_bitwise[0]) &&
         $stable(cout_adder) &&
         $changed(out_not[0]))
        |-> $changed(final_output[0])
    );

endmodule