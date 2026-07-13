module invert_msb_sva (
    input logic [3:0] i_binary,
    input logic [3:0] o_inverted
);
    // Output equals {~i_binary[3], i_binary[2:0]} on any input change.
    check_functional_mapping: assert property (
        @(posedge i_binary[0] or negedge i_binary[0] or
          posedge i_binary[1] or negedge i_binary[1] or
          posedge i_binary[2] or negedge i_binary[2] or
          posedge i_binary[3] or negedge i_binary[3])
        (o_inverted == {~i_binary[3], i_binary[2:0]})
    );

    // MSB of output is the inverse of input MSB.
    check_msb_inversion: assert property (
        @(posedge i_binary[0] or negedge i_binary[0] or
          posedge i_binary[1] or negedge i_binary[1] or
          posedge i_binary[2] or negedge i_binary[2] or
          posedge i_binary[3] or negedge i_binary[3])
        (o_inverted[3] == ~i_binary[3])
    );

    // Lower 3 bits of output equal input lower 3 bits.
    check_lower_bits_passthrough: assert property (
        @(posedge i_binary[0] or negedge i_binary[0] or
          posedge i_binary[1] or negedge i_binary[1] or
          posedge i_binary[2] or negedge i_binary[2] or
          posedge i_binary[3] or negedge i_binary[3])
        (o_inverted[2:0] == i_binary[2:0])
    );

    // If input is stable, output must be stable.
    check_stability_when_input_stable: assert property (
        @(posedge i_binary[0] or negedge i_binary[0] or
          posedge i_binary[1] or negedge i_binary[1] or
          posedge i_binary[2] or negedge i_binary[2] or
          posedge i_binary[3] or negedge i_binary[3])
        $stable(i_binary) |-> $stable(o_inverted)
    );

    // Output changes only if at least one input bit changes.
    check_output_change_requires_input_change: assert property (
        @(posedge i_binary[0] or negedge i_binary[0] or
          posedge i_binary[1] or negedge i_binary[1] or
          posedge i_binary[2] or negedge i_binary[2] or
          posedge i_binary[3] or negedge i_binary[3])
        $changed(o_inverted) |-> $changed(i_binary)
    );

    // If only MSB toggles, output MSB toggles and lower bits hold.
    check_only_msb_toggle_effect: assert property (
        @(posedge i_binary[0] or negedge i_binary[0] or
          posedge i_binary[1] or negedge i_binary[1] or
          posedge i_binary[2] or negedge i_binary[2] or
          posedge i_binary[3] or negedge i_binary[3])
        ($changed(i_binary[3]) && $stable(i_binary[2:0])) |-> ($changed(o_inverted[3]) && $stable(o_inverted[2:0]))
    );

    // If only lower bits toggle, output lower bits toggle and MSB holds.
    check_only_lower_bits_toggle_effect: assert property (
        @(posedge i_binary[0] or negedge i_binary[0] or
          posedge i_binary[1] or negedge i_binary[1] or
          posedge i_binary[2] or negedge i_binary[2] or
          posedge i_binary[3] or negedge i_binary[3])
        ($changed(i_binary[2:0]) && $stable(i_binary[3])) |-> ($changed(o_inverted[2:0]) && $stable(o_inverted[3]))
    );

    // If input is all zeros, output is {1,000}.
    check_zero_input_mapping: assert property (
        @(posedge i_binary[0] or negedge i_binary[0] or
          posedge i_binary[1] or negedge i_binary[1] or
          posedge i_binary[2] or negedge i_binary[2] or
          posedge i_binary[3] or negedge i_binary[3])
        (i_binary == 4'b0000) |-> (o_inverted == 4'b1000)
    );

    // If input is all ones, output is {0,111}.
    check_all_ones_input_mapping: assert property (
        @(posedge i_binary[0] or negedge i_binary[0] or
          posedge i_binary[1] or negedge i_binary[1] or
          posedge i_binary[2] or negedge i_binary[2] or
          posedge i_binary[3] or negedge i_binary[3])
        (i_binary == 4'b1111) |-> (o_inverted == 4'b0111)
    );

    // If input is 0001, output is 1001.
    check_one_input_mapping: assert property (
        @(posedge i_binary[0] or negedge i_binary[0] or
          posedge i_binary[1] or negedge i_binary[1] or
          posedge i_binary[2] or negedge i_binary[2] or
          posedge i_binary[3] or negedge i_binary[3])
        (i_binary == 4'b0001) |-> (o_inverted == 4'b1001)
    );

    // If input is 1000, output is 0100.
    check_eight_input_mapping: assert property (
        @(posedge i_binary[0] or negedge i_binary[0] or
          posedge i_binary[1] or negedge i_binary[1] or
          posedge i_binary[2] or negedge i_binary[2] or
          posedge i_binary[3] or negedge i_binary[3])
        (i_binary == 4'b1000) |-> (o_inverted == 4'b0100)
    );
endmodule