module dff2_sva (
    input logic        clk,
    input logic [1:0]  q,
    input logic [1:0]  in0,
    input logic [1:0]  in1,
    input logic        sel0,
    input logic        sel1
);

    // q updates according to the registered priority mux.
    check_next_state_function: assert property (
        @(posedge clk) 1'b1 |=> (q == $past(sel0 ? in0 : (sel1 ? in1 : q)))
    );

    // sel0 causes q to load in0 on the next sampled cycle.
    check_load_in0: assert property (
        @(posedge clk) sel0 |=> (q == $past(in0))
    );

    // sel1 causes q to load in1 when sel0 is not asserted.
    check_load_in1: assert property (
        @(posedge clk) (!sel0 && sel1) |=> (q == $past(in1))
    );

    // q holds its value when neither select is asserted.
    check_hold_value: assert property (
        @(posedge clk) (!sel0 && !sel1) |=> (q == $past(q))
    );

endmodule