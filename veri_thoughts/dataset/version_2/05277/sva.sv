module register_bank_sva (
    input logic        clock,
    input logic [31:0] data,
    input logic [4:0]  rdaddress,
    input logic [4:0]  wraddress,
    input logic        wren,
    input logic [31:0] q
);

    // A write updates q with the written data two cycles later.
    check_write_reaches_q_after_two_cycles: assert property (
        @(posedge clock) wren |-> ##2 (q == $past(data, 2))
    );

    // Without a write, q holds its prior sampled value two cycles later.
    check_no_write_holds_q_after_two_cycles: assert property (
        @(posedge clock) !wren |-> ##2 (q == $past(q))
    );

    // Back-to-back writes appear on q in the same order, two cycles later.
    check_back_to_back_writes_preserve_order: assert property (
        @(posedge clock) (wren ##1 wren) |=> ((q == $past(data, 2)) ##1 (q == $past(data, 2)))
    );

    // A write followed by an idle cycle makes q take the write data, then hold it.
    check_write_then_idle_holds_value: assert property (
        @(posedge clock) (wren ##1 !wren) |=> ((q == $past(data, 2)) ##1 (q == $past(q)))
    );

    // An idle cycle before a write delays any q update until the write reaches q.
    check_idle_then_write_delays_update: assert property (
        @(posedge clock) (!wren ##1 wren) |=> ((q == $past(q)) ##1 (q == $past(data, 2)))
    );

endmodule