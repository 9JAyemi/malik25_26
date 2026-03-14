module Approx_adder_sva #(
    parameter W = 26,
    parameter LowL = 16
) (
    // Verification clock/reset (DUT has no clock/reset; these are for SVA sampling)
    input  logic CLK,
    input  logic RESETn,

    // DUT ports
    input  logic                  add_sub,
    input  logic [W-1:0]          in1,
    input  logic [W-1:0]          in2,
    input  logic [W:0]            res
);

    ///// Generic combinational invariants (hold for all configurations) /////
    // Output is a pure function: same inputs on consecutive cycles => same output.
    check_deterministic_output: assert property (
        @(posedge CLK) disable iff (!RESETn)
        ({add_sub,in1,in2} == $past({add_sub,in1,in2})) |-> (res == $past(res))
    );

    // Low result bits unchanged if add_sub and low input slices are unchanged.
    check_low_bits_unchanged_when_low_inputs_unchanged: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (add_sub == $past(add_sub) &&
         in1[LowL-1:0] == $past(in1[LowL-1:0]) &&
         in2[LowL-1:0] == $past(in2[LowL-1:0])) |-> (res[LowL-1:0] == $past(res[LowL-1:0]))
    );

    // Output only changes when at least one input (including add_sub) changes.
    check_output_changes_only_on_input_change: assert property (
        @(posedge CLK) disable iff (!RESETn)
        $changed(res) |-> $changed({add_sub,in1,in2})
    );

    // Low bits change only if add_sub or low input slices change.
    check_low_bits_change_only_on_low_input_or_op_change: assert property (
        @(posedge CLK) disable iff (!RESETn)
        $changed(res[LowL-1:0]) |-> $changed({add_sub,in1[LowL-1:0],in2[LowL-1:0]})
    );

    // No unknowns on output when inputs are known.
    check_no_x_on_output_when_inputs_known: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (!$isunknown({add_sub,in1,in2})) |-> (!$isunknown(res))
    );

    // Repeated inputs two cycles apart yield repeated outputs (memoryless).
    check_two_cycle_repetition_memoryless: assert property (
        @(posedge CLK) disable iff (!RESETn)
        ({add_sub,in1,in2} == $past({add_sub,in1,in2},2)) |-> (res == $past(res,2))
    );

    ///// Exact implementation checks (active only when no approximate macro is defined) /////
`ifdef ACAIN16Q4
`elsif ETAIIN16Q4
`elsif ETAIIN16Q8
`elsif ACAIIN16Q4
`elsif ACAIIN16Q8
`elsif GDAN16M4P4
`elsif GDAN16M4P8
`elsif GeArN16R2P4
`elsif GeArN16R4P4
`elsif GeArN16R4P8
`elsif LOALPL4
`elsif LOALPL5
`elsif LOALPL6
`elsif LOALPL7
`elsif LOALPL8
`elsif LOALPL9
`elsif LOALPL10
`elsif LOALPL11
`elsif LOALPL12
`elsif LOALPL13
`elsif GeArN16R6P4
`else
    // In add mode, res equals zero-extended exact sum.
    check_add_exact_value: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (add_sub == 1'b0) |-> (res == ({1'b0,in1} + {1'b0,in2}))
    );

    // In sub mode, res equals zero-extended exact difference.
    check_sub_exact_value_zero_extended: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (add_sub == 1'b1) |-> (res == {1'b0,(in1 - in2)})
    );

    // In sub mode, MSB of res is always 0 due to zero-extension.
    check_sub_msb_zero: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (add_sub == 1'b1) |-> (res[W] == 1'b0)
    );

    // In add mode, LSB equals XOR of input LSBs.
    check_add_lsb_xor: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (add_sub == 1'b0) |-> (res[0] == (in1[0] ^ in2[0]))
    );

    // In sub mode, LSB equals XOR of input LSBs.
    check_sub_lsb_xor: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (add_sub == 1'b1) |-> (res[0] == (in1[0] ^ in2[0]))
    );

    // In add mode, adding zero leaves operand unchanged (zero-extended).
    check_add_zero_identity: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (add_sub == 1'b0 && in2 == '0) |-> (res == {1'b0,in1})
    );

    // In sub mode, subtracting self yields zero (zero-extended).
    check_sub_self_zero: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (add_sub == 1'b1 && in1 == in2) |-> (res == '0)
    );
`endif

endmodule