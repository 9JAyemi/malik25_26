module parity_check_sva (
    input logic CLK,
    input logic RESETn,
    input logic [7:0] data,
    input logic parity_error
);
    // parity_error equals the reduction XOR of data (handles X/Z via case equality).
    check_parity_equals_reduction: assert property (
        @(posedge CLK) disable iff (!RESETn) (parity_error === (^data))
    );

    // If data is stable, parity_error must be stable.
    check_parity_stable_when_data_stable: assert property (
        @(posedge CLK) disable iff (!RESETn) $stable(data) |-> $stable(parity_error)
    );

    // Parity toggle between cycles equals the parity of the bits that changed.
    check_parity_toggle_matches_bit_changes: assert property (
        @(posedge CLK) disable iff (!RESETn) ((parity_error ^ $past(parity_error)) === ^(data ^ $past(data)))
    );

    // Fully known data implies parity_error is known (no X/Z).
    check_known_data_implies_known_parity: assert property (
        @(posedge CLK) disable iff (!RESETn) (!$isunknown(data)) |-> (!$isunknown(parity_error))
    );

    // All-zero data has even parity -> parity_error is 0.
    check_zero_data_even_parity: assert property (
        @(posedge CLK) disable iff (!RESETn) (data == 8'h00) |-> (parity_error == 1'b0)
    );

    // All-ones (8'hFF) has even parity for 8 bits -> parity_error is 0.
    check_allones_even_parity: assert property (
        @(posedge CLK) disable iff (!RESETn) (data == 8'hFF) |-> (parity_error == 1'b0)
    );

    // Exactly one '1' in data (odd weight) -> parity_error is 1.
    check_onehot_odd_parity: assert property (
        @(posedge CLK) disable iff (!RESETn) $onehot(data) |-> (parity_error == 1'b1)
    );

    // Exactly one '0' in data (seven ones, odd) -> parity_error is 1.
    check_onecold_odd_parity: assert property (
        @(posedge CLK) disable iff (!RESETn) $onehot(~data) |-> (parity_error == 1'b1)
    );

    // Complementing all bits between cycles (8 toggles, even) preserves parity_error.
    check_complement_preserves_parity_for_even_width: assert property (
        @(posedge CLK) disable iff (!RESETn) (data == ~$past(data)) |-> (parity_error === $past(parity_error))
    );
endmodule