module counter_sva (
    input logic       CLK,
    input logic       CLR,
    input logic       LD,
    input logic [3:0] DATA,
    input logic [3:0] Q0,
    input logic [3:0] Q1,
    input logic [3:0] Q2,
    input logic [3:0] Q3
);

    // Reset clears all pipeline outputs on the next cycle.
    check_reset_clears_pipeline: assert property (
        @(posedge CLK) CLR |=> (Q0 == 4'b0000) && (Q1 == 4'b0000) && (Q2 == 4'b0000) && (Q3 == 4'b0000)
    );

    // A load cycle captures DATA into Q0 on the next cycle.
    check_load_captures_data_to_q0: assert property (
        @(posedge CLK) disable iff (CLR) LD |=> (Q0 == $past(DATA))
    );

    // A count cycle updates Q0 from the previous Q3 plus one.
    check_count_advances_q0_from_q3: assert property (
        @(posedge CLK) disable iff (CLR) !LD |=> (Q0 == ($past(Q3) + 4'b0001))
    );

    // Q1 shifts in the previous Q0 whenever reset is not active.
    check_q1_shifts_previous_q0: assert property (
        @(posedge CLK) disable iff (CLR) 1'b1 |=> (Q1 == $past(Q0))
    );

    // Q2 shifts in the previous Q1 whenever reset is not active.
    check_q2_shifts_previous_q1: assert property (
        @(posedge CLK) disable iff (CLR) 1'b1 |=> (Q2 == $past(Q1))
    );

    // Q3 shifts in the previous Q2 whenever reset is not active.
    check_q3_shifts_previous_q2: assert property (
        @(posedge CLK) disable iff (CLR) 1'b1 |=> (Q3 == $past(Q2))
    );

endmodule