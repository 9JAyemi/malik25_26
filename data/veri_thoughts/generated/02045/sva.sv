module four_bit_adder_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic Cin,
    input logic CLK,
    input logic [3:0] S,
    input logic Cout
);
    // Clock: CLK; no reset in RTL
    // Sequential: registered 4-bit adder updated on posedge CLK
    // Behavior: {Cout,S} is the 5-bit sum of A+B+Cin (observed one cycle later)

    ///// Functional correctness /////
    // Outputs equal prior-cycle 5-bit sum of inputs.
    check_sum_pipelined: assert property (
        @(posedge CLK) {Cout, S} == ($past(A) + $past(B) + $past(Cin))
    );

    // S equals the lower 4 bits of the prior-cycle sum.
    check_sum_low_bits: assert property (
        @(posedge CLK) S == (($past(A) + $past(B) + $past(Cin))[3:0])
    );

    // Cout equals the MSB of the prior-cycle 5-bit sum.
    check_carry_msb: assert property (
        @(posedge CLK) Cout == (($past(A) + $past(B) + $past(Cin))[4])
    );

    // Cout asserted iff the prior-cycle sum exceeds 15.
    check_carry_threshold: assert property (
        @(posedge CLK) Cout == (($past(A) + $past(B) + $past(Cin)) >= 5'd16)
    );

    ///// Temporal consistency /////
    // If A,B,Cin are stable over a cycle, the next output sample is unchanged.
    check_hold_when_inputs_stable: assert property (
        @(posedge CLK) ($stable(A) && $stable(B) && $stable(Cin)) |-> ##1 ({Cout, S} == $past({Cout, S}))
    );

    // With A,B stable, a rising Cin increments the next output by 1.
    check_increment_on_cin_rise: assert property (
        @(posedge CLK) ($stable(A) && $stable(B) && ($past(Cin) == 1'b0) && (Cin == 1'b1)) |-> ##1 ({Cout, S} == $past({Cout, S}) + 5'd1)
    );

    // With A,B stable, a falling Cin decrements the next output by 1.
    check_decrement_on_cin_fall: assert property (
        @(posedge CLK) ($stable(A) && $stable(B) && ($past(Cin) == 1'b1) && (Cin == 1'b0)) |-> ##1 ({Cout, S} == $past({Cout, S}) - 5'd1)
    );

    ///// Corner cases /////
    // Prior-cycle inputs all zero produce zero output.
    check_zero_case: assert property (
        @(posedge CLK) ($past(A) == 4'd0 && $past(B) == 4'd0 && $past(Cin) == 1'b0) |-> ({Cout, S} == 5'd0)
    );

    // Prior-cycle A=15, B=15, Cin=1 produce 31 (all ones) at output.
    check_max_case: assert property (
        @(posedge CLK) ($past(A) == 4'd15 && $past(B) == 4'd15 && $past(Cin) == 1'b1) |-> ({Cout, S} == 5'd31)
    );

    ///// Algebraic consistency /////
    // Swapping A and B across cycles with Cin stable leaves next output unchanged.
    check_commutativity_swap: assert property (
        @(posedge CLK) ((A == $past(B)) && (B == $past(A)) && (Cin == $past(Cin))) |-> ##1 ({Cout, S} == $past({Cout, S}))
    );

endmodule