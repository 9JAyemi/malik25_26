module synchronous_counter_sva (
    input logic CLK,
    input logic RST,
    input logic LOAD,
    input logic EN,
    input logic [3:0] DATA_IN,
    input logic [3:0] DATA_OUT
);
    // Clock: CLK (posedge). Reset: RST active-high, synchronous. Logic: sequential.
    // Behavior: RST->0; LOAD->DATA_OUT:=DATA_IN; else if EN->count with wrap; else hold.

    // On RST high at a clock, DATA_OUT becomes 0 on the next cycle.
    reset_clears_next: assert property (
        @(posedge CLK) RST |=> (DATA_OUT == 4'b0000)
    );

    // LOAD updates DATA_OUT with DATA_IN on the next cycle.
    load_captures_data_in: assert property (
        @(posedge CLK) disable iff (RST) LOAD |=> (DATA_OUT == $past(DATA_IN))
    );

    // LOAD has priority over EN when both are asserted.
    load_overrides_en: assert property (
        @(posedge CLK) disable iff (RST) (LOAD && EN) |=> (DATA_OUT == $past(DATA_IN))
    );

    // With EN and not LOAD, non-max value increments by 1 on the next cycle.
    en_increments_nonmax: assert property (
        @(posedge CLK) disable iff (RST) (EN && !LOAD && (DATA_OUT != 4'hF)) |=> (DATA_OUT == $past(DATA_OUT) + 4'd1)
    );

    // With EN and not LOAD, 4'hF wraps to 0 on the next cycle.
    en_wraps_at_max_to_zero: assert property (
        @(posedge CLK) disable iff (RST) (EN && !LOAD && (DATA_OUT == 4'hF)) |=> (DATA_OUT == 4'h0)
    );

    // With neither EN nor LOAD, DATA_OUT holds its previous value.
    holds_when_idle: assert property (
        @(posedge CLK) disable iff (RST) (!EN && !LOAD) |=> (DATA_OUT == $past(DATA_OUT))
    );

    // With EN and not LOAD, DATA_OUT must change (either increment or wrap).
    en_causes_change: assert property (
        @(posedge CLK) disable iff (RST) (EN && !LOAD) |=> (DATA_OUT != $past(DATA_OUT))
    );

    // When not RESET and not LOAD, the only allowed transitions are hold, +1, or wrap.
    allowed_transitions_without_load: assert property (
        @(posedge CLK) disable iff (RST)
            (!RST && !LOAD) |=> (
                // hold when EN==0
                (( !$past(EN) ) && (DATA_OUT == $past(DATA_OUT))) ||
                // +1 when EN==1 and not max
                (( $past(EN) && ($past(DATA_OUT) != 4'hF) ) && (DATA_OUT == $past(DATA_OUT) + 4'd1)) ||
                // wrap to 0 when EN==1 and max
                (( $past(EN) && ($past(DATA_OUT) == 4'hF) ) && (DATA_OUT == 4'h0))
            )
    );

endmodule