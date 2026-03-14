module xor_gate_sva (
    input logic A,
    input logic B,
    input logic EN,
    input logic CLK,
    input logic Z
);
    // Z matches previous-cycle function: EN ? (A^B) : 0.
    check_functional_nextstate: assert property (
        @(posedge CLK) disable iff ($initstate)
            Z == ($past(EN) ? ($past(A) ^ $past(B)) : 1'b0)
    );

    // When previously disabled, Z must be 0.
    check_zero_when_disabled_prev: assert property (
        @(posedge CLK) disable iff ($initstate)
            (!$past(EN)) |-> (Z == 1'b0)
    );

    // When previously enabled, Z equals previous A^B.
    check_xor_when_enabled_prev: assert property (
        @(posedge CLK) disable iff ($initstate)
            ($past(EN)) |-> (Z == ($past(A) ^ $past(B)))
    );

    // If Z is 1 now, previous EN was 1 and previous A!=B.
    check_z_high_implies_prev_enable_unequal: assert property (
        @(posedge CLK) disable iff ($initstate)
            (Z == 1'b1) |-> ($past(EN) && ($past(A) ^ $past(B)))
    );

    // If Z is 0 now with previous EN=1, previous A==B.
    check_z_low_with_enable_implies_prev_inputs_equal: assert property (
        @(posedge CLK) disable iff ($initstate)
            ($past(EN) && (Z == 1'b0)) |-> (~($past(A) ^ $past(B)))
    );

    // A rising edge on Z only occurs if previously EN=1 and A!=B.
    check_rose_z_cause: assert property (
        @(posedge CLK) disable iff ($initstate)
            $rose(Z) |-> ($past(EN) && ($past(A) ^ $past(B)))
    );

    // A falling edge on Z only occurs if previously EN=0 or A==B.
    check_fell_z_cause: assert property (
        @(posedge CLK) disable iff ($initstate)
            $fell(Z) |-> ((!$past(EN)) || (~($past(A) ^ $past(B))))
    );
endmodule