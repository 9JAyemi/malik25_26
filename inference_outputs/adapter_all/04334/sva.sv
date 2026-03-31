module RCB_FRL_TrainingPattern_sva (
    input logic CLK,
    input logic RST,
    input logic [7:0] DATA_OUT
);
    // On reset, DATA_OUT is driven to 0 on the next cycle.
    reset_clears_next: assert property (
        @(posedge CLK) RST |=> (DATA_OUT == 8'h00)
    );

    // If previous cycle was not reset and DATA_OUT was not 0xf4, next cycle is 0xf4.
    map_not_f4_to_f4: assert property (
        @(posedge CLK) disable iff (RST) (!$past(RST) && ($past(DATA_OUT) != 8'hf4)) |-> (DATA_OUT == 8'hf4)
    );

    // If previous cycle was not reset and DATA_OUT was 0xf4, next cycle is 0xc2.
    map_f4_to_c2: assert property (
        @(posedge CLK) disable iff (RST) (!$past(RST) && ($past(DATA_OUT) == 8'hf4)) |-> (DATA_OUT == 8'hc2)
    );

    // If previous cycle was not reset and DATA_OUT was 0xc2, next cycle is 0xf4.
    map_c2_to_f4: assert property (
        @(posedge CLK) disable iff (RST) (!$past(RST) && ($past(DATA_OUT) == 8'hc2)) |-> (DATA_OUT == 8'hf4)
    );

    // If previous cycle was not reset and DATA_OUT was not 0xf4 or 0xc2, next cycle is 0xf4.
    map_other_to_f4: assert property (
        @(posedge CLK) disable iff (RST) (!$past(RST) && ($past(DATA_OUT) != 8'hf4) && ($past(DATA_OUT) != 8'hc2)) |-> (DATA_OUT == 8'hf4)
    );

    // If previous cycle was not reset and DATA_OUT was 0xf4, next cycle is not 0xf4 (must be 0xc2).
    f4_implies_next_c2: assert property (
        @(posedge CLK) disable iff (RST) (!$past(RST) && ($past(DATA_OUT) == 8'hf4)) |-> (DATA_OUT != 8'hf4)
    );

    // If previous cycle was not reset and DATA_OUT was 0xc2, next cycle is not 0xc2 (must be 0xf4).
    c2_implies_next_f4: assert property (
        @(posedge CLK) disable iff (RST) (!$past(RST) && ($past(DATA_OUT) == 8'hc2)) |-> (DATA_OUT != 8'hc2)
    );

    // If previous cycle was not reset and DATA_OUT was 0xf4, next cycle is not 0xf4 (must be 0xc2).
    f4_implies_next_not_f4: assert property (
        @(posedge CLK) disable iff (RST) (!$past(RST) && ($past(DATA_OUT) == 8'hf4)) |-> (DATA_OUT != 8'hf4)
    );

    // If previous cycle was not reset and DATA_OUT was 0xc2, next cycle is not 0xc2 (must be 0xf4).
    c2_implies_next_not_c2: assert property (
        @(posedge CLK) disable iff (RST) (!$past(RST) && ($past(DATA_OUT) == 8'hc2)) |-> (DATA_OUT != 8'hc2)
    );

    // If previous cycle was not reset and DATA_OUT was 0xf4, next cycle is 0xc2.
    f4_implies_next_c2: assert property (
        @(posedge CLK) disable iff (RST) (!$past(RST) && ($past(DATA_OUT) == 8'hf4)) |-> (DATA_OUT == 8'hc2)
    );

    // If previous cycle was not reset and DATA_OUT was 0xc2, next cycle is 0xf4.
    c2_implies_next_f4: assert property (
        @(posedge CLK) disable iff (RST) (!$past(RST) && ($past(DATA_OUT) == 8'hc2)) |-> (DATA_OUT == 8'hf4)
    );
endmodule