module myDFFSR_sva (
    input logic D,
    input logic C,
    input logic R,
    input logic S,
    input logic Q
);

    // Active-high synchronous reset clears Q.
    check_reset_clears_q: assert property (
        @(posedge C) R |=> (Q == 1'b0)
    );

    // With reset low, set forces Q high.
    check_set_sets_q: assert property (
        @(posedge C) disable iff (R) S |=> (Q == 1'b1)
    );

    // With reset and set low, D=1 is loaded into Q.
    check_data_one_loads_q: assert property (
        @(posedge C) disable iff (R) (!S && D) |=> (Q == 1'b1)
    );

    // With reset and set low, D=0 is loaded into Q.
    check_data_zero_loads_q: assert property (
        @(posedge C) disable iff (R) (!S && !D) |=> (Q == 1'b0)
    );

endmodule