module lfsr_sva(
    input logic        CLK,
    input logic        RST_N,
    input logic        START,
    input logic        STOP,
    input logic [15:0] DATA_OUT,
    input logic [15:0] state
);

    // Reset clears state and DATA_OUT on the next clock.
    check_reset_clears_registers: assert property (
        @(posedge CLK) !RST_N |=> (state == 16'h0000) && (DATA_OUT == 16'h0000)
    );

    // START clears state on the next clock.
    check_start_clears_state: assert property (
        @(posedge CLK) disable iff (!RST_N) START |=> (state == 16'h0000)
    );

    // START makes DATA_OUT capture the previous state value.
    check_start_captures_previous_state: assert property (
        @(posedge CLK) disable iff (!RST_N) START |=> (DATA_OUT == $past(state))
    );

    // STOP clears both registers when START is low.
    check_stop_clears_registers: assert property (
        @(posedge CLK) disable iff (!RST_N) (!START && STOP) |=> (state == 16'h0000) && (DATA_OUT == 16'h0000)
    );

    // With no START or STOP, state follows the implemented concatenation update.
    check_run_updates_state: assert property (
        @(posedge CLK) disable iff (!RST_N) (!START && !STOP) |=> 
            (state == {1'b0, $past(state[13:0]), ($past(state[15]) ^ $past(state[13]))})
    );

    // With no START or STOP, DATA_OUT captures the previous state.
    check_run_updates_data_out: assert property (
        @(posedge CLK) disable iff (!RST_N) (!START && !STOP) |=> (DATA_OUT == $past(state))
    );

endmodule