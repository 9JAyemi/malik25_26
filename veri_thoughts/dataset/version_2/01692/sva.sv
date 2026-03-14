module receiver_sva (
    input logic        clock,
    input logic        trxClock,
    input logic        reset,
    input logic        rx,
    input logic  [7:0] op,
    input logic [31:0] data,
    input logic        execute,
    input logic  [2:0] state,
    input logic  [9:0] counter,
    input logic  [3:0] bitcount,
    input logic  [2:0] bytecount
);
    // State encodings (must match RTL)
    localparam [2:0]
        INIT      = 3'h0,
        WAITSTOP  = 3'h1,
        WAITSTART = 3'h2,
        WAITBEGIN = 3'h3,
        READBYTE  = 3'h4,
        ANALYZE   = 3'h5,
        READY     = 3'h6;

    // execute is high exactly while state is READY.
    check_execute_matches_ready: assert property (
        @(posedge clock) disable iff (reset) execute == (state == READY)
    );

    // After reset deassertion, enter WAITSTOP with cleared regs/outputs next cycle.
    check_post_reset_init: assert property (
        @(posedge clock) disable iff (reset)
            $fell(reset) |-> ##1 (state == WAITSTOP && op == 8'h00 && data == 32'h0 && execute == 1'b0
                                   && counter == 10'd0 && bitcount == 4'd0 && bytecount == 3'd0)
    );

    // From INIT, advance to WAITSTOP in one cycle.
    check_init_to_waitstop: assert property (
        @(posedge clock) disable iff (reset) (state == INIT) |-> ##1 (state == WAITSTOP)
    );

    // In WAITSTOP, rx=0 holds state.
    check_waitstop_hold_when_rx0: assert property (
        @(posedge clock) disable iff (reset) (state == WAITSTOP && (rx == 1'b0)) |-> ##1 (state == WAITSTOP)
    );

    // In WAITSTOP, rx=1 advances to WAITSTART.
    check_waitstop_to_waitstart: assert property (
        @(posedge clock) disable iff (reset) (state == WAITSTOP && rx) |-> ##1 (state == WAITSTART)
    );

    // In WAITSTART, rx=1 holds WAITSTART.
    check_waitstart_hold_when_rx1: assert property (
        @(posedge clock) disable iff (reset) (state == WAITSTART && rx) |-> ##1 (state == WAITSTART)
    );

    // In WAITSTART, rx=0 advances to WAITBEGIN.
    check_waitstart_to_waitbegin: assert property (
        @(posedge clock) disable iff (reset) (state == WAITSTART && !rx) |-> ##1 (state == WAITBEGIN)
    );

    // While staying in WAITBEGIN with trxClock=1, counter increments by 1.
    check_waitbegin_counter_inc_on_trx: assert property (
        @(posedge clock) disable iff (reset)
            ($past(state) == WAITBEGIN && $past(trxClock) && (state == WAITBEGIN)) |-> (counter == $past(counter) + 10'd1)
    );

    // While staying in WAITBEGIN with trxClock=0, counter holds.
    check_waitbegin_counter_hold_without_trx: assert property (
        @(posedge clock) disable iff (reset)
            ($past(state) == WAITBEGIN && !$past(trxClock) && (state == WAITBEGIN)) |-> (counter == $past(counter))
    );

    // On transition from WAITBEGIN to READBYTE, counter resets to 0.
    check_waitbegin_to_readbyte_counter_reset: assert property (
        @(posedge clock) disable iff (reset)
            ($past(state) == WAITBEGIN && state == READBYTE) |-> (counter == 10'd0)
    );

    // READBYTE: on sample complete at bitcount==8, go to ANALYZE, bump bytecount, reset counter, op/data stable.
    check_readbyte_to_analyze_on_bit8: assert property (
        @(posedge clock) disable iff (reset)
            ($past(state) == READBYTE && (bitcount == $past(bitcount) + 1) && ($past(bitcount) == 4'h8))
            |-> (state == ANALYZE && counter == 10'd0 && bytecount == $past(bytecount) + 1 && op == $past(op) && data == $past(data))
    );

    // READBYTE: on sample (not bit 8) for first byte, shift rx into op and hold data.
    check_readbyte_shift_into_op: assert property (
        @(posedge clock) disable iff (reset)
            ($past(state) == READBYTE && (bitcount == $past(bitcount) + 1) && ($past(bitcount) != 4'h8) && ($past(bytecount) == 3'h0))
            |-> (state == READBYTE && counter == 10'd0 && op == { $past(rx), $past(op[7:1]) } && data == $past(data))
    );

    // READBYTE: on sample (not bit 8) for data bytes, shift rx into data and hold op.
    check_readbyte_shift_into_data: assert property (
        @(posedge clock) disable iff (reset)
            ($past(state) == READBYTE && (bitcount == $past(bitcount) + 1) && ($past(bitcount) != 4'h8) && ($past(bytecount) != 3'h0))
            |-> (state == READBYTE && counter == 10'd0 && op == $past(op) && data == { $past(rx), $past(data[31:1]) })
    );

    // ANALYZE: counters reset to 0 in the following cycle.
    check_analyze_resets_counters_next: assert property (
        @(posedge clock) disable iff (reset) (state == ANALYZE) |-> ##1 (counter == 10'd0 && bitcount == 4'd0)
    );

    // ANALYZE: if bytecount==5 then go to READY.
    check_analyze_ready_on_bytecount5: assert property (
        @(posedge clock) disable iff (reset) (state == ANALYZE && (bytecount == 3'h5)) |-> ##1 (state == READY)
    );

    // ANALYZE: if bytecount!=5 and op[7]==0 then go to READY.
    check_analyze_ready_on_op7_zero: assert property (
        @(posedge clock) disable iff (reset) (state == ANALYZE && (bytecount != 3'h5) && (op[7] == 1'b0)) |-> ##1 (state == READY)
    );

    // ANALYZE: else go to WAITSTOP.
    check_analyze_to_waitstop: assert property (
        @(posedge clock) disable iff (reset) (state == ANALYZE && (bytecount != 3'h5) && (op[7] == 1'b1)) |-> ##1 (state == WAITSTOP)
    );

    // In READY, outputs op and data remain stable.
    check_ready_holds_outputs: assert property (
        @(posedge clock) disable iff (reset) (state == READY) |-> ($stable(op) && $stable(data))
    );

    // In READY and counter!=10, stay in READY.
    check_ready_stay_until_cnt10: assert property (
        @(posedge clock) disable iff (reset) (state == READY && (counter != 4'd10)) |-> ##1 (state == READY)
    );

    // In READY and counter==10, transition to INIT.
    check_ready_to_init_on_cnt10: assert property (
        @(posedge clock) disable iff (reset) (state == READY && (counter == 4'd10)) |-> ##1 (state == INIT)
    );

    // While remaining in READY, counter increments by 1 each cycle.
    check_ready_counter_increments: assert property (
        @(posedge clock) disable iff (reset) ($past(state) == READY && state == READY) |-> (counter == $past(counter) + 10'd1)
    );

    // Rising edge of execute holds high at least one more cycle.
    check_execute_min_width: assert property (
        @(posedge clock) disable iff (reset) $rose(execute) |-> ##1 execute
    );

    // Each execute pulse ends within 12 cycles.
    check_execute_max_width: assert property (
        @(posedge clock) disable iff (reset) $rose(execute) |-> ##[1:12] !execute
    );

    // After execute falls, next cycle state is INIT.
    check_execute_fall_to_init: assert property (
        @(posedge clock) disable iff (reset) $fell(execute) |-> ##1 (state == INIT)
    );

    // Two cycles after execute falls, op and data are cleared to 0.
    check_outputs_cleared_after_execute_fall: assert property (
        @(posedge clock) disable iff (reset) $fell(execute) |-> ##2 (op == 8'h00 && data == 32'h0)
    );

    // In consecutive WAITSTOP cycles, outputs remain stable.
    check_waitstop_outputs_stable: assert property (
        @(posedge clock) disable iff (reset) ($past(state) == WAITSTOP && state == WAITSTOP) |-> ($stable(op) && $stable(data))
    );

    // In consecutive WAITSTART cycles, outputs remain stable.
    check_waitstart_outputs_stable: assert property (
        @(posedge clock) disable iff (reset) ($past(state) == WAITSTART && state == WAITSTART) |-> ($stable(op) && $stable(data))
    );

    // In consecutive WAITBEGIN cycles, outputs remain stable.
    check_waitbegin_outputs_stable: assert property (
        @(posedge clock) disable iff (reset) ($past(state) == WAITBEGIN && state == WAITBEGIN) |-> ($stable(op) && $stable(data))
    );
endmodule