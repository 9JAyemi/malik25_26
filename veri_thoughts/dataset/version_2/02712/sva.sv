module parity_checker_sva (
    input logic CLK,          // external sampling clock for SVA (RTL has no clock)
    input logic [7:0] data_in,
    input logic sel_b1,
    input logic parity
);
    // Analysis: no clock/reset in RTL; purely combinational always @(*).
    // Behavior: xor_out = XOR of data_in[7:0]; parity = xor_out when sel_b1==0, else ~xor_out.

    // When sel_b1==0, parity equals XOR of data_in bits.
    check_parity_sel0: assert property (
        @(posedge CLK) (!sel_b1) |-> (parity == ^data_in)
    );

    // When sel_b1==1, parity equals inverted XOR of data_in bits.
    check_parity_sel1: assert property (
        @(posedge CLK) (sel_b1) |-> (parity == ~(^data_in))
    );

    // Parity matches the Boolean equation parity == (^data_in) ^ sel_b1.
    check_parity_equation: assert property (
        @(posedge CLK) 1'b1 |-> (parity == ((^data_in) ^ sel_b1))
    );

    // If inputs are stable, parity must be stable.
    check_stable_when_inputs_stable: assert property (
        @(posedge CLK) ($stable(data_in) && $stable(sel_b1)) |-> $stable(parity)
    );

    // Output changes only if at least one input changes.
    check_output_change_requires_input_change: assert property (
        @(posedge CLK) $changed(parity) |-> (!$stable(data_in) || !$stable(sel_b1))
    );

    // If only sel_b1 toggles, parity toggles.
    check_toggle_when_only_sel_changes: assert property (
        @(posedge CLK) ($changed(sel_b1) && $stable(data_in)) |-> (parity == ~$past(parity))
    );

    // If sel_b1 is stable and an odd number of data bits toggle, parity toggles.
    check_toggle_on_odd_data_changes: assert property (
        @(posedge CLK) ($stable(sel_b1) && (^(data_in ^ $past(data_in)))) |-> (parity == ~$past(parity))
    );

    // If sel_b1 is stable and an even number of data bits toggle, parity does not toggle.
    check_no_toggle_on_even_data_changes: assert property (
        @(posedge CLK) ($stable(sel_b1) && !(^(data_in ^ $past(data_in)))) |-> (parity == $past(parity))
    );

    // If XOR of data_in is 0, parity equals sel_b1.
    check_xor_zero_parity_equals_sel: assert property (
        @(posedge CLK) ((^data_in) == 1'b0) |-> (parity == sel_b1)
    );

    // If XOR of data_in is 1, parity equals inverse of sel_b1.
    check_xor_one_parity_equals_not_sel: assert property (
        @(posedge CLK) ((^data_in) == 1'b1) |-> (parity == ~sel_b1)
    );
endmodule