module odd_parity_sva (
    input logic CLK,
    input logic RESETn,
    input logic [7:0] in,
    input logic [8:0] out
);
    ///// Functional mapping checks /////
    // Upper 8 bits of out pass through input byte.
    check_data_passthrough: assert property (
        @(posedge CLK) disable iff (!RESETn) out[8:1] == in
    );
    // Parity bit equals XOR reduction of input bits.
    check_parity_from_in: assert property (
        @(posedge CLK) disable iff (!RESETn) out[0] == ^in
    );
    // Parity bit equals XOR reduction of out's data field.
    check_parity_matches_data: assert property (
        @(posedge CLK) disable iff (!RESETn) out[0] == ^out[8:1]
    );
    // Overall out has even parity (XOR of all 9 bits is 0).
    check_out_even_parity: assert property (
        @(posedge CLK) disable iff (!RESETn) (^out) == 1'b0
    );

    ///// Temporal consistency /////
    // If input is stable, output must be stable (pure combinational mapping).
    check_stable_in_out_stable: assert property (
        @(posedge CLK) disable iff (!RESETn) $stable(in) |-> $stable(out)
    );
    // Single-bit input flip toggles the parity bit.
    check_single_bit_flip_toggles_parity: assert property (
        @(posedge CLK) disable iff (!RESETn) $onehot(in ^ $past(in)) |-> (out[0] ^ $past(out[0]))
    );
    // Data field changes exactly mirror input changes.
    check_data_change_matches: assert property (
        @(posedge CLK) disable iff (!RESETn) ((out[8:1] ^ $past(out[8:1])) == (in ^ $past(in)))
    );
    // Parity bit toggle equals parity of input change mask.
    check_parity_change_equals_change_parity: assert property (
        @(posedge CLK) disable iff (!RESETn) (out[0] ^ $past(out[0])) == ^(in ^ $past(in))
    );
    // Even-number (non-zero) of input bit flips do not toggle parity bit.
    check_even_changes_keep_parity: assert property (
        @(posedge CLK) disable iff (!RESETn)
            (((in ^ $past(in)) != 8'b0) && (^(in ^ $past(in)) == 1'b0)) |-> (out[0] == $past(out[0]))
    );

    ///// Corner cases /////
    // All-zero input yields zero data and zero parity.
    check_zero_input_output: assert property (
        @(posedge CLK) disable iff (!RESETn) (in == 8'h00) |-> ((out[8:1] == 8'h00) && (out[0] == 1'b0))
    );
    // All-ones input passes through with zero parity.
    check_all_ones_input_output: assert property (
        @(posedge CLK) disable iff (!RESETn) (in == 8'hFF) |-> ((out[8:1] == 8'hFF) && (out[0] == 1'b0))
    );
endmodule