module RCB_FRL_TrainingPattern_sva (
    input logic CLK,
    input logic RST,
    input logic [7:0] DATA_OUT
);

// Clock: CLK (posedge). Reset: RST active-high synchronous.
    // Logic: Sequential; next-state depends on current DATA_OUT.

    // On reset, DATA_OUT is driven to 0 on the next cycle.
    reset_clears_next: assert property (
        @(posedge CLK) RST |=> (DATA_OUT == 8'h00)
    );

// When not in reset and DATA_OUT is 0xf4, next value is 0xc2.
    next_c2_when_f4: assert property (
        @(posedge CLK) disable iff (RST) (DATA_OUT == 8'hf4) |=> (DATA_OUT == 8'hc2)
    );

// When not in reset and DATA_OUT is not 0xf4, next value is 0xf4.
    next_f4_when_not_f4: assert property (
        @(posedge CLK) disable iff (RST) (DATA_OUT != 8'hf4) |=> (DATA_OUT == 8'hf4)
    );

// When not in reset, DATA_OUT must be either 0xf4 or 0xc2 on the next cycle.
    next_value_legal: assert property (
        @(posedge CLK) disable iff (RST) 1'b1 |=> ((DATA_OUT == 8'hf4) || (DATA_OUT == 8'hc2))
    );

// If DATA_OUT is 0xc2, it must have come from a previous 0xf4 (not in reset).
    c2_implies_prev_f4: assert property (
        @(posedge CLK) disable iff (RST) (DATA_OUT == 8'hc2) |-> ##1 (DATA_OUT == 8'hf4)
    );

// If DATA_OUT is 0xf4 and previous was not 0xf4, previous must have been 0xc2.
    f4_implies_prev_c2: assert property (
        @(posedge CLK) disable iff (RST) (DATA_OUT == 8'hf4) && $past(DATA_OUT != 8'hf4) |-> ##1 (DATA_OUT == 8'hc2)
    );

endmodule
