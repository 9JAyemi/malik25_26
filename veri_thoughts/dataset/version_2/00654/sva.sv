module parity_generator_sva (
    input logic CLK,       // External sampling clock for SVA
    input logic RESETn,    // External active-low reset for SVA gating
    input logic in1,
    input logic in2,
    input logic in3,
    input logic in4,
    input logic parity
);
    ///// Functional parity checks /////
    // Parity equals XOR of inputs (odd parity).
    check_parity_matches_xor: assert property (
        @(posedge CLK) disable iff (!RESETn) parity == (in1 ^ in2 ^ in3 ^ in4)
    );

    // Exactly one input HIGH implies parity HIGH.
    check_onehot_high: assert property (
        @(posedge CLK) disable iff (!RESETn) $onehot({in1,in2,in3,in4}) |-> (parity == 1'b1)
    );

    // Exactly two inputs HIGH implies parity LOW.
    check_two_high_low: assert property (
        @(posedge CLK) disable iff (!RESETn) ((in1 + in2 + in3 + in4) == 2) |-> (parity == 1'b0)
    );

    // Exactly three inputs HIGH implies parity HIGH.
    check_three_high: assert property (
        @(posedge CLK) disable iff (!RESETn) ((in1 + in2 + in3 + in4) == 3) |-> (parity == 1'b1)
    );

    // All inputs equal (all 0 or all 1) implies parity LOW.
    check_all_equal_low: assert property (
        @(posedge CLK) disable iff (!RESETn) ((in1 == in2) && (in2 == in3) && (in3 == in4)) |-> (parity == 1'b0)
    );

    ///// Temporal consistency w.r.t. input changes /////
    // If inputs are stable cycle-to-cycle, parity must be stable.
    check_stable_inputs_hold_parity: assert property (
        @(posedge CLK) disable iff (!RESETn) $stable({in1,in2,in3,in4}) |-> $stable(parity)
    );

    // If exactly one input toggles, parity must toggle.
    check_one_bit_toggle_parity_toggle: assert property (
        @(posedge CLK) disable iff (!RESETn)
            $onehot({in1 ^ $past(in1), in2 ^ $past(in2), in3 ^ $past(in3), in4 ^ $past(in4)}) |-> (parity != $past(parity))
    );

    // If an even number of inputs toggle, parity must be unchanged.
    check_even_flips_keep_parity: assert property (
        @(posedge CLK) disable iff (!RESETn)
            (( $countones({in1 ^ $past(in1), in2 ^ $past(in2), in3 ^ $past(in3), in4 ^ $past(in4)}) % 2 ) == 0)
            |-> (parity == $past(parity))
    );
endmodule