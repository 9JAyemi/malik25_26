module UART_Rx_sva #(
    parameter int N = 5,
    parameter logic [N-1:0] Full = 5'd29
)(
    input logic Reset,
    input logic Clk,

    input logic [7:0] Data,
    input logic       Ready,
    input logic       Ack,
    input logic       Rx,

    // Internal signals from DUT
    input logic       tRx,
    input logic       tAck,
    input logic [7:0] Temp,
    input logic [N-1:0] Count,
    input logic [2:0] BitCount,
    input logic       NewData,
    input logic [1:0] State,
    input logic       tReset
);
    // Local copies of state encodings for readability
    localparam logic [1:0] Idle      = 2'b00;
    localparam logic [1:0] StartBit  = 2'b01;
    localparam logic [1:0] Receiving = 2'b11;
    localparam logic [1:0] Done      = 2'b10;

    ///// Reset behavior /////
    // On synchronous reset, clear state and outputs next cycle.
    reset_seq_clear: assert property (
        @(posedge Clk) tReset |=> (Data == 8'h00) && (Ready == 1'b0) && (NewData == 1'b0) && (Count == {N{1'b0}}) && (State == Idle)
    );

    ///// Sampling flops /////
    // tRx is Rx delayed by one cycle.
    check_tRx_is_delayed_Rx: assert property (
        @(posedge Clk) disable iff (tReset) tRx == $past(Rx)
    );
    // tAck is Ack delayed by one cycle.
    check_tAck_is_delayed_Ack: assert property (
        @(posedge Clk) disable iff (tReset) tAck == $past(Ack)
    );

    ///// State encoding /////
    // State must be one of the defined encodings.
    check_state_encoding: assert property (
        @(posedge Clk) disable iff (tReset) (State inside {Idle, StartBit, Receiving, Done})
    );

    ///// Ready/Ack handshake /////
    // Ready clears one cycle after tAck is HIGH while Ready is HIGH.
    check_ready_clears_on_tAck: assert property (
        @(posedge Clk) disable iff (tReset) (Ready && tAck) |=> !Ready
    );
    // Ready holds HIGH if tAck is LOW.
    check_ready_holds_without_tAck: assert property (
        @(posedge Clk) disable iff (tReset) (Ready && !tAck) |=> Ready
    );
    // A falling Ready must be caused by tAck in the previous cycle.
    check_ready_fall_caused_by_tAck: assert property (
        @(posedge Clk) disable iff (tReset) $fell(Ready) |-> $past(Ready && tAck)
    );

    ///// Start bit detection /////
    // StartBit can only be entered from Idle when tRx is LOW.
    check_startbit_entry_from_idle_only: assert property (
        @(posedge Clk) disable iff (tReset) (State == StartBit && $past(State) != StartBit) |-> $past(State == Idle && !tRx)
    );
    // From Idle with start detected and Count==0, preset Count to half and go to StartBit.
    check_idle_to_startbit_half_count: assert property (
        @(posedge Clk) disable iff (tReset) $past(State == Idle && !tRx && (Count == {N{1'b0}})) |=> (State == StartBit) && (Count == {1'b0, Full[N-1:1]})
    );
    // In StartBit with Count==0 and Rx HIGH, return to Idle next cycle.
    check_startbit_abort_on_high_Rx: assert property (
        @(posedge Clk) disable iff (tReset) $past(State == StartBit && (Count == {N{1'b0}}) && (Rx == 1'b1)) |=> (State == Idle)
    );
    // In StartBit with Count==0 and Rx LOW, enter Receiving, reload Count, and clear BitCount.
    check_startbit_to_receiving_on_low_Rx: assert property (
        @(posedge Clk) disable iff (tReset) $past(State == StartBit && (Count == {N{1'b0}}) && (Rx == 1'b0)) |=> (State == Receiving) && (Count == Full) && (BitCount == 3'd0)
    );

    ///// Receiving bits /////
    // In Receiving at Count==0, reload Count to Full.
    check_receiving_reload_count: assert property (
        @(posedge Clk) disable iff (tReset) $past(State == Receiving && (Count == {N{1'b0}})) |=> (Count == Full)
    );
    // In Receiving at Count==0, shift in tRx into Temp.
    check_receiving_shift: assert property (
        @(posedge Clk) disable iff (tReset) $past(State == Receiving && (Count == {N{1'b0}})) |=> (Temp == {$past(tRx), $past(Temp[7:1])})
    );
    // When the last bit is sampled, assert NewData and go to Done.
    check_receiving_done_on_last_bit: assert property (
        @(posedge Clk) disable iff (tReset) $past(State == Receiving && (Count == {N{1'b0}}) && (&BitCount)) |=> (NewData == 1'b1) && (State == Done)
    );

    ///// Done/Idle transition /////
    // In Done, when tRx is HIGH, return to Idle next cycle.
    check_done_to_idle_on_high_tRx: assert property (
        @(posedge Clk) disable iff (tReset) $past(State == Done && tRx) |=> (State == Idle)
    );

    ///// Data/Ready generation in Idle /////
    // In Idle with NewData and no tAck and Ready LOW, latch Temp to Data, raise Ready, and clear NewData.
    check_data_latch_in_idle_when_newdata_no_ack: assert property (
        @(posedge Clk) disable iff (tReset) $past(State == Idle && NewData && !tAck && !Ready) |=> (Data == $past(Temp)) && (Ready == 1'b1) && (NewData == 1'b0)
    );
    // When Ready rises, Data must equal previous Temp and NewData must be cleared.
    check_ready_rise_latches_data_and_clears_newdata: assert property (
        @(posedge Clk) disable iff (tReset) $rose(Ready) |-> (Data == $past(Temp)) && (NewData == 1'b0)
    );

    ///// Counter behavior /////
    // When Count is non-zero, it decrements by 1 next cycle.
    check_count_decrements_when_nonzero: assert property (
        @(posedge Clk) disable iff (tReset) $past(Count != {N{1'b0}}) |=> (Count == ($past(Count) - {{(N-1){1'b0}},1'b1}))
    );

    ///// Temp write points /////
    // Temp only updates when sampling a bit in Receiving at Count==0.
    check_temp_changes_only_on_sample: assert property (
        @(posedge Clk) disable iff (tReset) $changed(Temp) |-> $past(State == Receiving && (Count == {N{1'b0}}))
    );
endmodule