module flag_register_sva (
    input logic IN_FLAG,
    input logic LD,
    input logic SET,
    input logic CLR,
    input logic CLK,
    input logic OUT_FLAG
);

    // LD has highest priority and loads a 1 on the next cycle.
    check_load_one: assert property (
        @(posedge CLK) (LD && IN_FLAG) |=> OUT_FLAG
    );

    // LD has highest priority and loads a 0 on the next cycle.
    check_load_zero: assert property (
        @(posedge CLK) (LD && !IN_FLAG) |=> !OUT_FLAG
    );

    // SET drives the flag high when LD is low.
    check_set_when_selected: assert property (
        @(posedge CLK) (!LD && SET) |=> OUT_FLAG
    );

    // CLR drives the flag low when LD and SET are low.
    check_clear_when_selected: assert property (
        @(posedge CLK) (!LD && !SET && CLR) |=> !OUT_FLAG
    );

    // With no control active, a high flag holds its value.
    check_hold_high: assert property (
        @(posedge CLK) (!LD && !SET && !CLR && OUT_FLAG) |=> OUT_FLAG
    );

    // With no control active, a low flag holds its value.
    check_hold_low: assert property (
        @(posedge CLK) (!LD && !SET && !CLR && !OUT_FLAG) |=> !OUT_FLAG
    );

endmodule