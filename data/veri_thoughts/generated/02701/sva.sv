module sky130_fd_sc_ls__a22oi_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2
);
    // Functional equivalence: Y == ~((A1 & A2) | (B1 & B2))
    check_functional_equivalence: assert property (
        @(posedge clk) disable iff (1'b0) Y == ~((A1 & A2) | (B1 & B2))
    );

    // Y must be LOW if either A-pair or B-pair is HIGH
    check_y_low_when_any_pair_high: assert property (
        @(posedge clk) disable iff (1'b0) ((A1 & A2) || (B1 & B2)) |-> (Y == 1'b0)
    );

    // Y must be HIGH if both A-pair and B-pair are not HIGH
    check_y_high_when_no_pair_high: assert property (
        @(posedge clk) disable iff (1'b0) (!(A1 & A2) && !(B1 & B2)) |-> (Y == 1'b1)
    );

    // A-pair HIGH alone forces Y LOW
    check_y_low_when_a_pair_high: assert property (
        @(posedge clk) disable iff (1'b0) (A1 & A2) |-> (Y == 1'b0)
    );

    // B-pair HIGH alone forces Y LOW
    check_y_low_when_b_pair_high: assert property (
        @(posedge clk) disable iff (1'b0) (B1 & B2) |-> (Y == 1'b0)
    );

    // If A2=0 and B2=0, Y must be HIGH regardless of A1/B1
    check_y_high_when_a2_b2_zero: assert property (
        @(posedge clk) disable iff (1'b0) (!A2 && !B2) |-> (Y == 1'b1)
    );

    // If A1=0 and B1=0, Y must be HIGH regardless of A2/B2
    check_y_high_when_a1_b1_zero: assert property (
        @(posedge clk) disable iff (1'b0) (!A1 && !B1) |-> (Y == 1'b1)
    );

    // A1 rising with A2=1 and B-pair=0 causes Y to FALL
    check_a1_rise_causes_y_fall: assert property (
        @(posedge clk) disable iff (1'b0)
            $rose(A1) && A2 && $past(A2) && !(B1 & B2) && !$past(B1 & B2) |-> $fell(Y)
    );

    // A1 falling with A2=1 and B-pair=0 causes Y to RISE
    check_a1_fall_causes_y_rise: assert property (
        @(posedge clk) disable iff (1'b0)
            $fell(A1) && A2 && $past(A2) && !(B1 & B2) && !$past(B1 & B2) |-> $rose(Y)
    );

    // A2 rising with A1=1 and B-pair=0 causes Y to FALL
    check_a2_rise_causes_y_fall: assert property (
        @(posedge clk) disable iff (1'b0)
            $rose(A2) && A1 && $past(A1) && !(B1 & B2) && !$past(B1 & B2) |-> $fell(Y)
    );

    // A2 falling with A1=1 and B-pair=0 causes Y to RISE
    check_a2_fall_causes_y_rise: assert property (
        @(posedge clk) disable iff (1'b0)
            $fell(A2) && A1 && $past(A1) && !(B1 & B2) && !$past(B1 & B2) |-> $rose(Y)
    );
endmodule