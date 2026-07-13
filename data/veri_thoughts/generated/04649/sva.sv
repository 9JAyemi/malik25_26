module D_behavior_sva (
    input logic D,
    input logic Clk,
    input logic Qa,
    input logic Qb,
    input logic Qc
);

    // Qa captures D on the next rising clock edge.
    check_qa_captures_d: assert property (
        @(posedge Clk) disable iff (1'b0)
        1'b1 |=> (Qa == $past(D))
    );

    // Qb captures Qa on the next rising clock edge.
    check_qb_captures_qa: assert property (
        @(posedge Clk) disable iff (1'b0)
        1'b1 |=> (Qb == $past(Qa))
    );

    // Qc captures Qb on the next rising clock edge.
    check_qc_captures_qb: assert property (
        @(posedge Clk) disable iff (1'b0)
        1'b1 |=> (Qc == $past(Qb))
    );

    // Qb is D delayed by two rising clock edges.
    check_qb_is_d_delayed_two_cycles: assert property (
        @(posedge Clk) disable iff (1'b0)
        1'b1 |=> ##1 (Qb == $past(D, 2))
    );

    // Qc is D delayed by three rising clock edges.
    check_qc_is_d_delayed_three_cycles: assert property (
        @(posedge Clk) disable iff (1'b0)
        1'b1 |=> ##2 (Qc == $past(D, 3))
    );

endmodule