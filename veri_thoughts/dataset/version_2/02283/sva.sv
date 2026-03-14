module my_module_sva (
    input logic clk,
    input logic lower_ina,
    input logic lower_io,
    input logic lower_out,
    input logic sec_ina,
    input logic sec_io,
    input logic sec_out
);
    // lower_out equals lower_ina OR lower_io
    check_lower_out_def: assert property (
        @(posedge clk) lower_out === (lower_ina | lower_io)
    );
    // sec_out equals sec_ina OR sec_io
    check_sec_out_def: assert property (
        @(posedge clk) sec_out === (sec_ina | sec_io)
    );

    // If any lower input is 1, lower_out must be 1
    check_lower_out_one_if_any_one: assert property (
        @(posedge clk) ((lower_ina === 1'b1) || (lower_io === 1'b1)) |-> (lower_out === 1'b1)
    );
    // If any sec input is 1, sec_out must be 1
    check_sec_out_one_if_any_one: assert property (
        @(posedge clk) ((sec_ina === 1'b1) || (sec_io === 1'b1)) |-> (sec_out === 1'b1)
    );

    // lower_out is 0 only if both lower inputs are 0
    check_lower_out_zero_only_if_both_zero: assert property (
        @(posedge clk) (lower_out === 1'b0) |-> ((lower_ina === 1'b0) && (lower_io === 1'b0))
    );
    // sec_out is 0 only if both sec inputs are 0
    check_sec_out_zero_only_if_both_zero: assert property (
        @(posedge clk) (sec_out === 1'b0) |-> ((sec_ina === 1'b0) && (sec_io === 1'b0))
    );

    // If lower inputs are stable, lower_out is stable
    check_lower_out_stable_when_inputs_stable: assert property (
        @(posedge clk) ($stable(lower_ina) && $stable(lower_io)) |-> $stable(lower_out)
    );
    // If sec inputs are stable, sec_out is stable
    check_sec_out_stable_when_inputs_stable: assert property (
        @(posedge clk) ($stable(sec_ina) && $stable(sec_io)) |-> $stable(sec_out)
    );

    // A change on lower_out requires a change on some lower input
    check_lower_out_change_requires_input_change: assert property (
        @(posedge clk) $changed(lower_out) |-> ($changed(lower_ina) || $changed(lower_io))
    );
    // A change on sec_out requires a change on some sec input
    check_sec_out_change_requires_input_change: assert property (
        @(posedge clk) $changed(sec_out) |-> ($changed(sec_ina) || $changed(sec_io))
    );

    // With known lower inputs, lower_out must be known
    check_lower_out_known_when_inputs_known: assert property (
        @(posedge clk) (!$isunknown(lower_ina) && !$isunknown(lower_io)) |-> !$isunknown(lower_out)
    );
    // With known sec inputs, sec_out must be known
    check_sec_out_known_when_inputs_known: assert property (
        @(posedge clk) (!$isunknown(sec_ina) && !$isunknown(sec_io)) |-> !$isunknown(sec_out)
    );
endmodule