module parity_checker_sva (
    input logic CLK,          // External sampling clock (DUT has no clock/reset)
    input logic [3:0] data,
    input logic parity
);
    // Parity equals XOR reduction of data (4-state exact equality).
    check_parity_matches_reduction: assert property (
        @(posedge CLK) disable iff (1'b0) parity === (^data)
    );

    // Parity not X/Z when all data bits are known.
    check_parity_known_when_data_known: assert property (
        @(posedge CLK) disable iff (1'b0) (!$isunknown(data)) |-> (!$isunknown(parity))
    );

    // If inputs do not change, parity does not change (no storage; pure function).
    check_parity_stable_when_inputs_stable: assert property (
        @(posedge CLK) disable iff (1'b0) (data === $past(data)) |-> (parity === $past(parity))
    );

    // A single-bit flip in data causes parity to toggle.
    check_parity_toggles_on_single_bit_flip: assert property (
        @(posedge CLK) disable iff (1'b0)
            (!$isunknown(data) && !$isunknown($past(data)) && ($countones(data ^ $past(data)) == 1))
            |-> (parity !== $past(parity))
    );

    // Two-bit flips in data leave parity unchanged (even parity preservation).
    check_parity_stable_on_two_bit_flip: assert property (
        @(posedge CLK) disable iff (1'b0)
            (!$isunknown(data) && !$isunknown($past(data)) && ($countones(data ^ $past(data)) == 2))
            |-> (parity === $past(parity))
    );
endmodule