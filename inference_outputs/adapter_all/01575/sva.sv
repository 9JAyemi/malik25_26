module parity_check_sva (
    input logic [7:0] data,
    input logic parity_error
);
    // parity_error equals XOR reduction of data.
    check_parity_definition: assert property (
        @(posedge data[0]) parity_error == (^data)
    );

    // If data is stable, parity_error must be stable.
    check_stable_when_data_stable: assert property (
        @(posedge data[0]) $stable(data) |-> $stable(parity_error)
    );

    // If parity_error changes, data must have changed.
    check_error_change_implies_data_change: assert property (
        @(posedge data[0]) $changed(parity_error) |-> $changed(data)
    );

    // If data changes, parity_error must change.
    check_data_change_implies_error_change: assert property (
        @(posedge data[0]) $changed(data) |-> $changed(parity_error)
    );

    // If data is all zeros, parity_error must be 0.
    check_zero_data_implies_no_error: assert property (
        @(posedge data[0]) (data == 8'h00) |-> (parity_error == 1'b0)
    );

    // If data is all ones, parity_error must be 0.
    check_all_ones_implies_no_error: assert property (
        @(posedge data[0]) (data == 8'hFF) |-> (parity_error == 1'b0)
    );

    // If data is even (XOR == 0), parity_error must be 0.
    check_even_parity_implies_no_error: assert property (
        @(posedge data[0]) (^data == 1'b0) |-> (parity_error == 1'b0)
    );

    // If data is odd (XOR == 1), parity_error must be 1.
    check_odd_parity_implies_error: assert property (
        @(posedge data[0]) (^data == 1'b1) |-> (parity_error == 1'b1)
    );

    // If data toggles exactly one bit, parity_error must toggle.
    check_single_bit_toggle_toggles_error: assert property (
        @(posedge data[0]) $onehot($changed(data)) |-> $changed(parity_error)
    );

    // If data toggles two bits, parity_error must not change.
    check_two_bit_toggle_keeps_error: assert property (
        @(posedge data[0]) $onehot(~$changed(data)) |-> !$changed(parity_error)
    );
endmodule