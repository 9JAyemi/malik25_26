module top_module_assertions (
    input logic        clk,
    input logic        reset,
    input logic [7:0]  final_output,
    input logic [3:0]  counter_out,
    input logic [7:0]  register_out
);

    // Counter goes to zero on the cycle after a reset clock.
    check_counter_resets_to_zero: assert property (
        @(posedge clk) reset |=> (counter_out == 4'h0)
    );

    // The register loads 8'h34 on the cycle after a reset clock.
    check_register_loads_reset_value: assert property (
        @(posedge clk) reset |=> (register_out == 8'h34)
    );

    // Final output is zero after the reset values take effect.
    check_final_output_resets_to_zero: assert property (
        @(posedge clk) reset |=> (final_output == 8'h00)
    );

    // The counter increments by one across consecutive non-reset cycles.
    check_counter_increments: assert property (
        @(posedge clk) disable iff (reset)
        (!$initstate && !$past(reset)) |-> (counter_out == ($past(counter_out) + 4'd1))
    );

    // The register holds its value when reset was not asserted on the prior cycle.
    check_register_holds_without_reset: assert property (
        @(posedge clk) disable iff (reset)
        (!$initstate && !$past(reset)) |-> (register_out === $past(register_out))
    );

    // Any register change must come from a reset update to 8'h34.
    check_register_changes_only_on_reset: assert property (
        @(posedge clk)
        (!$initstate && (register_out !== $past(register_out))) |-> ($past(reset) && (register_out == 8'h34))
    );

    // Final output matches the AND of zero-extended counter_out and register_out.
    check_final_output_matches_and: assert property (
        @(posedge clk) (final_output === ({4'h0, counter_out} & register_out))
    );

    // The upper nibble of final_output is always zero.
    check_final_output_upper_nibble_zero: assert property (
        @(posedge clk) (final_output[7:4] == 4'h0)
    );

    // With register value 8'h34, masked low bits stay zero.
    check_masked_output_bits_zero: assert property (
        @(posedge clk) (register_out == 8'h34) |-> ((final_output[3] == 1'b0) && (final_output[1:0] == 2'b00))
    );

    // With register value 8'h34, output bit 2 follows counter_out[2].
    check_masked_output_bit2_tracks_counter: assert property (
        @(posedge clk) (register_out == 8'h34) |-> (final_output[2] == counter_out[2])
    );

endmodule

bind top_module top_module_assertions top_module_assertions_inst (
    .clk(clk),
    .reset(reset),
    .final_output(final_output),
    .counter_out(counter_out),
    .register_out(register_out)
);