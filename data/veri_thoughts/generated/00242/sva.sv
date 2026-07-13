module input_buffer_assertions (
    input logic in,
    input logic en,
    input logic out,
    input logic stored_out
);

    // When en is low just before it rises, out must reflect the stored value.
    check_disabled_path_uses_stored_out: assert property (
        @(posedge en) out === stored_out
    );

    // When en is high just before it falls, out must reflect the live input.
    check_enabled_path_uses_input: assert property (
        @(negedge en) out === in
    );

    // On each later enable pulse, stored_out must still hold the input captured on the prior pulse.
    check_stored_out_keeps_last_captured_input: assert property (
        @(posedge en) 1'b1 |=> stored_out === $past(in)
    );

    // On each later enable pulse, out must present the value captured on the prior pulse while en is low.
    check_output_keeps_last_captured_input_while_disabled: assert property (
        @(posedge en) 1'b1 |=> out === $past(in)
    );

endmodule