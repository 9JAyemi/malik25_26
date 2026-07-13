module binary_adder_4bit_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic CI,
    input logic CLK,
    input logic [3:0] SUM,
    input logic CO
);
    // CO never has a rising edge (MSB of C is never driven to 1 by the RTL).
    check_co_never_rises: assert property (
        @(posedge CLK) !$rose(CO)
    );

    // If CO is HIGH now, it must be LOW on the next cycle.
    check_co_clears_next_if_high: assert property (
        @(posedge CLK) (CO == 1'b1) |=> (CO == 1'b0)
    );

    // Once CO is LOW, it remains LOW on the next cycle.
    check_co_low_sticky: assert property (
        @(posedge CLK) (CO == 1'b0) |=> (CO == 1'b0)
    );

    // From any time, CO becomes LOW within two cycles and thus cannot persist HIGH.
    check_co_eventually_low_within_two: assert property (
        @(posedge CLK) 1'b1 |-> ##[0:2] (CO == 1'b0)
    );

    // After any falling edge of CO, it stays LOW forever.
    check_co_stays_low_after_fall: assert property (
        @(posedge CLK) $fell(CO) |-> (CO == 1'b0)[*1:$]
    );

    // If A and B are zero for three consecutive cycles and CO is LOW at the first, SUM is zero on the third.
    check_sum_zero_after_three_zero_inputs_when_co_zero: assert property (
        @(posedge CLK)
            ((CO == 1'b0) && (A == 4'b0000) && (B == 4'b0000)) ##1
            ((A == 4'b0000) && (B == 4'b0000)) ##1
            ((A == 4'b0000) && (B == 4'b0000) && (SUM == 4'b0000))
    );
endmodule