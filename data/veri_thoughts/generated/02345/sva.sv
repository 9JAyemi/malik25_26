module top_module_sva (
    input logic CLK,
    input logic [3:0] in,
    input logic [7:0] sel,
    input logic [1023:0] out
);
    // Low 256 bits equal in[0] ? (1<<sel) : 0.
    check_low_out_function: assert property (
        @(posedge CLK) disable iff (1'b0) out[255:0] == (in[0] ? (256'b1 << sel) : 256'b0)
    );
    // Upper 768 bits are always zero.
    check_upper_bits_zero: assert property (
        @(posedge CLK) disable iff (1'b0) out[1023:256] == 768'b0
    );
    // The bit indexed by sel matches in[0].
    check_sel_bit_matches_in0: assert property (
        @(posedge CLK) disable iff (1'b0) out[sel] == in[0]
    );
    // No other low bits (besides sel) are set.
    check_no_other_low_bits_set: assert property (
        @(posedge CLK) disable iff (1'b0) (out[255:0] & ~((256'b1) << sel)) == 256'b0
    );
    // When in[0] is 0, all output bits are 0.
    check_out_zero_when_in0_zero: assert property (
        @(posedge CLK) disable iff (1'b0) (in[0] == 1'b0) |-> (out == 1024'b0)
    );
    // When in[0] is 1, output is exactly one-hot.
    check_onehot_when_in0_one: assert property (
        @(posedge CLK) disable iff (1'b0) (in[0] == 1'b1) |-> $onehot(out)
    );
    // If in[0] is 1 and sel changes, out must change.
    check_out_changes_on_sel_change_when_in0_one: assert property (
        @(posedge CLK) disable iff (1'b0) (in[0] == 1'b1 && $changed(sel)) |-> $changed(out)
    );
    // If sel is stable and in[0] toggles, out must change.
    check_out_changes_on_in0_toggle: assert property (
        @(posedge CLK) disable iff (1'b0) (!$changed(sel) && $changed(in[0])) |-> $changed(out)
    );
    // If in and sel are stable, out must be stable.
    check_out_stable_when_inputs_stable: assert property (
        @(posedge CLK) disable iff (1'b0) (!$changed(in) && !$changed(sel)) |-> !$changed(out)
    );
    // Changes on in[3:1] alone must not affect out.
    check_out_ignores_in3to1: assert property (
        @(posedge CLK) disable iff (1'b0) (!$changed(in[0]) && !$changed(sel) && $changed(in[3:1])) |-> !$changed(out)
    );
endmodule