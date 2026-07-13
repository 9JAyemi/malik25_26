module binary_adder_4bit_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic CLK,
    input logic RST,
    input logic [3:0] S
);
    // S is 0 on the cycle after any cycle with RST=1 (synchronous reset effect).
    check_reset_next_cycle_zero: assert property (
        @(posedge CLK) $past(RST) |-> (S == 4'b0000)
    );

    // On the cycle reset deasserts (1->0), S is 0 (was cleared by prior reset cycle).
    check_reset_release_zero: assert property (
        @(posedge CLK) $fell(RST) |-> (S == 4'b0000)
    );

    // When not in reset in the previous cycle, S equals (A+B) from the previous cycle (mod 16).
    check_sum_updates_from_prev_inputs: assert property (
        @(posedge CLK) disable iff (RST) $past(!RST) |-> (S == ( ($past(A) + $past(B)) [3:0] ))
    );

    // After reset deasserts, the first computed sum appears one cycle later.
    check_post_reset_first_sum: assert property (
        @(posedge CLK) disable iff (RST) $fell(RST) |=> (S == ( ($past(A) + $past(B)) [3:0] ))
    );

    // If the previous two sums are equal and neither of those cycles were in reset, S is unchanged.
    check_stable_when_prev_sums_equal: assert property (
        @(posedge CLK) disable iff (RST)
            ($past(!RST) && $past(!RST,2) &&
             ( ( ($past(A,1) + $past(B,1)) [3:0] ) == ( ($past(A,2) + $past(B,2)) [3:0] ) ))
            |-> (S == $past(S))
    );

    // Specific case: when previous A=F and B=F with no reset, S=E (30 mod 16).
    check_max_plus_max_wrap: assert property (
        @(posedge CLK) disable iff (RST)
            ($past(!RST) && ($past(A) == 4'hF) && ($past(B) == 4'hF))
            |-> (S == 4'hE)
    );

    // Specific case: when previous A=4 and B=3 with no reset, S=7.
    check_simple_add_example: assert property (
        @(posedge CLK) disable iff (RST)
            ($past(!RST) && ($past(A) == 4'h4) && ($past(B) == 4'h3))
            |-> (S == 4'h7)
    );

    // Specific wrap example: when previous A=9 and B=8 with no reset, S=1 (17 mod 16).
    check_wrap_example: assert property (
        @(posedge CLK) disable iff (RST)
            ($past(!RST) && ($past(A) == 4'h9) && ($past(B) == 4'h8))
            |-> (S == 4'h1)
    );

    // Specific zero case: when previous A=0 and B=0 with no reset, S=0.
    check_zero_plus_zero: assert property (
        @(posedge CLK) disable iff (RST)
            ($past(!RST) && ($past(A) == 4'h0) && ($past(B) == 4'h0))
            |-> (S == 4'h0)
    );
endmodule