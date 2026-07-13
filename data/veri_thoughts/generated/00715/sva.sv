module top_module_sva (
    input logic CLK,
    input logic RESETn,
    input logic [31:0] in,
    input logic [31:0] out,
    input logic enable,
    input logic [31:0] final_output
);
    // Helper to compute byte-swapped value of a 32-bit word.
    function automatic [31:0] swap_bytes (input [31:0] din);
        swap_bytes = {din[7:0], din[15:8], din[23:16], din[31:24]};
    endfunction

    ///// Byte swap rules /////
    // out must be the byte-swapped version of in.
    check_byte_swap_mapping_full: assert property (
        @(posedge CLK) disable iff (!RESETn) out == swap_bytes(in)
    );
    // Byte swap is an involution: in must equal byte-swap of out.
    check_byte_swap_symmetry: assert property (
        @(posedge CLK) disable iff (!RESETn) in == swap_bytes(out)
    );
    // High byte of out equals low byte of in.
    check_out_high_byte_mapping: assert property (
        @(posedge CLK) disable iff (!RESETn) out[31:24] == in[7:0]
    );
    // Low byte of out equals high byte of in.
    check_out_low_byte_mapping: assert property (
        @(posedge CLK) disable iff (!RESETn) out[7:0] == in[31:24]
    );
    // If out changes between cycles, in must have changed.
    check_out_change_implies_in_change: assert property (
        @(posedge CLK) disable iff (!RESETn) (out != $past(out)) |-> (in != $past(in))
    );
    // Toggling enable alone (with stable in) must not change out.
    check_out_independent_of_enable_toggle: assert property (
        @(posedge CLK) disable iff (!RESETn) ((in == $past(in)) && (enable != $past(enable))) |-> (out == $past(out))
    );

    ///// XOR gating rules /////
    // final_output must equal enable ? (in ^ out) : 0.
    check_final_output_function: assert property (
        @(posedge CLK) disable iff (!RESETn) final_output == (enable ? (in ^ out) : 32'h0000_0000)
    );
    // Nonzero final_output implies enable is asserted.
    check_nonzero_final_output_implies_enable: assert property (
        @(posedge CLK) disable iff (!RESETn) (final_output != 32'h0000_0000) |-> enable
    );
    // final_output equals enable ? (in ^ byte_swap(in)) : 0.
    check_final_output_with_swapped_in: assert property (
        @(posedge CLK) disable iff (!RESETn) final_output == (enable ? (in ^ swap_bytes(in)) : 32'h0000_0000)
    );
    // With in and out stable, final_output changes only if enable toggles.
    check_final_output_change_requires_enable_toggle_when_inputs_stable: assert property (
        @(posedge CLK) disable iff (!RESETn) ((in == $past(in)) && (out == $past(out)) && (final_output != $past(final_output))) |-> (enable != $past(enable))
    );
endmodule