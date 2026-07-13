module ShiftRegister_sva (
    input  logic D,
    input  logic LOAD,
    input  logic CLK,
    input  logic [5:0] Q
);

    // If LOAD was 1 last cycle, Q loads all bits from D.
    check_load_writes_all_bits: assert property (
        @(posedge CLK) $past(1'b1,1,1'b0) && $past(LOAD,1,1'b0) |-> (Q == {6{$past(D,1,1'b0)}})
    );

    // If LOAD was 0 last cycle, Q shifts left with D entering bit 0.
    check_shift_nextstate_vector: assert property (
        @(posedge CLK) $past(1'b1,1,1'b0) && !$past(LOAD,1,1'b0) |-> (Q == {$past(Q,1,6'b0)[4:0], $past(D,1,1'b0)})
    );

    // On shift (LOAD was 0), MSB gets previous bit 4.
    check_shift_msb_propagate: assert property (
        @(posedge CLK) $past(1'b1,1,1'b0) && !$past(LOAD,1,1'b0) |-> (Q[5] == $past(Q,1,6'b0)[4])
    );

    // On shift (LOAD was 0), LSB gets previous D.
    check_shift_lsb_from_D: assert property (
        @(posedge CLK) $past(1'b1,1,1'b0) && !$past(LOAD,1,1'b0) |-> (Q[0] == $past(D,1,1'b0))
    );

    // If LOAD was 1 last cycle, both MSB and LSB equal D.
    check_load_sets_end_bits: assert property (
        @(posedge CLK) $past(1'b1,1,1'b0) && $past(LOAD,1,1'b0) |-> (Q[5] == $past(D,1,1'b0)) && (Q[0] == $past(D,1,1'b0))
    );

endmodule