module RCB_FRL_TrainingPattern_sva (
    input logic       CLK,
    input logic       RST,
    input logic [7:0] DATA_OUT
);

    // CLK is the only clock; RST is a synchronous active-high reset.
    // DATA_OUT is an 8-bit registered output.

    ///// Reset behavior /////

    // When reset is asserted, DATA_OUT must be 0 on the following clock.
    check_reset_clears_data_out: assert property (
        @(posedge CLK)
        RST |=> (DATA_OUT === 8'h00)
    );

    ///// Active-state behavior /////

    // In active mode, F4 must toggle to C2 on the next clock.
    check_f4_transitions_to_c2: assert property (
        @(posedge CLK) disable iff (RST)
        (DATA_OUT === 8'hf4) |=> (DATA_OUT === 8'hc2)
    );

    // In active mode, any value other than F4 must become F4 on the next clock.
    check_non_f4_transitions_to_f4: assert property (
        @(posedge CLK) disable iff (RST)
        (DATA_OUT !== 8'hf4) |=> (DATA_OUT === 8'hf4)
    );

endmodule