module flag_register_sva (
    input logic IN_FLAG,
    input logic LD,
    input logic SET,
    input logic CLR,
    input logic CLK,
    input logic OUT_FLAG
);

    // Load updates OUT_FLAG from IN_FLAG.
    check_load_updates_flag: assert property (
        @(posedge CLK) LD |=> (OUT_FLAG == $past(IN_FLAG))
    );

    // SET drives OUT_FLAG high when load is not selected.
    check_set_updates_flag: assert property (
        @(posedge CLK) (!LD && SET) |=> (OUT_FLAG == 1'b1)
    );

    // CLR drives OUT_FLAG low when neither load nor set is selected.
    check_clear_updates_flag: assert property (
        @(posedge CLK) (!LD && !SET && CLR) |=> (OUT_FLAG == 1'b0)
    );

    // OUT_FLAG holds its value when no control is asserted.
    check_hold_when_idle: assert property (
        @(posedge CLK) (!LD && !SET && !CLR) |=> (OUT_FLAG == $past(OUT_FLAG))
    );

    // LOAD has priority over SET and CLR.
    check_load_priority: assert property (
        @(posedge CLK) (LD && (SET || CLR)) |=> (OUT_FLAG == $past(IN_FLAG))
    );

    // SET has priority over CLR when load is not asserted.
    check_set_priority_over_clear: assert property (
        @(posedge CLK) (!LD && SET && CLR) |=> (OUT_FLAG == 1'b1)
    );

endmodule