module xor4_sva (
    input logic CLK,
    input logic RESETn,
    input logic X,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic AB,
    input logic CD,
    input logic ABCD
);

    ///// Structural equivalence to instantiated gates /////
    // AB equals A XOR B.
    check_ab_xor: assert property (
        @(posedge CLK) disable iff (!RESETn) AB == (A ^ B)
    );

    // CD equals C XOR D.
    check_cd_xor: assert property (
        @(posedge CLK) disable iff (!RESETn) CD == (C ^ D)
    );

    // ABCD equals AB XOR CD.
    check_abcd_xor: assert property (
        @(posedge CLK) disable iff (!RESETn) ABCD == (AB ^ CD)
    );

    // X is assigned directly from ABCD.
    check_output_assign: assert property (
        @(posedge CLK) disable iff (!RESETn) X == ABCD
    );

    ///// Functional parity property /////
    // X equals the XOR of A, B, C, and D.
    check_x_equals_xor4: assert property (
        @(posedge CLK) disable iff (!RESETn) X == ((A ^ B) ^ (C ^ D))
    );

    ///// Temporal consistency from combinational behavior /////
    // With reset previously deasserted, X's change equals parity of input changes.
    check_parity_change_equivalence: assert property (
        @(posedge CLK) disable iff (!RESETn)
            $past(RESETn) |-> ((X ^ $past(X)) == ((A ^ $past(A)) ^ (B ^ $past(B)) ^ (C ^ $past(C)) ^ (D ^ $past(D))))
    );

    // If inputs are stable, X remains stable.
    check_stable_inputs_hold_output: assert property (
        @(posedge CLK) disable iff (!RESETn)
            ($past(RESETn) && $stable(A) && $stable(B) && $stable(C) && $stable(D)) |-> $stable(X)
    );

    // If exactly one input toggles, X toggles.
    check_one_input_toggle_changes_output: assert property (
        @(posedge CLK) disable iff (!RESETn)
            ($past(RESETn) && ($countones({A ^ $past(A), B ^ $past(B), C ^ $past(C), D ^ $past(D)}) == 1)) |-> (X ^ $past(X))
    );

    // If exactly two inputs toggle, X does not change.
    check_two_input_toggle_keeps_output: assert property (
        @(posedge CLK) disable iff (!RESETn)
            ($past(RESETn) && ($countones({A ^ $past(A), B ^ $past(B), C ^ $past(C), D ^ $past(D)}) == 2)) |-> (X == $past(X))
    );

    // If all four inputs toggle, X does not change.
    check_four_input_toggle_keeps_output: assert property (
        @(posedge CLK) disable iff (!RESETn)
            ($past(RESETn) && ($countones({A ^ $past(A), B ^ $past(B), C ^ $past(C), D ^ $past(D)}) == 4)) |-> (X == $past(X))
    );

endmodule