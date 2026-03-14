module bram_controller_sva (
    input logic clk,
    input logic reset,
    input logic btn,
    input logic wea,
    input logic [3:0] addra,
    input logic [1:0] state_reg,
    input logic [3:0] counter
);
    // State encodings matching RTL
    localparam logic [1:0]
        idle = 2'b00,
        leer = 2'b01,
        fin  = 2'b10;

    ///// Reset behavior /////
    // On reset deassertion, outputs/state/counter return to defaults.
    check_reset_release_defaults: assert property (
        @(posedge clk) disable iff (reset)
            $fell(reset) |-> (addra == 4'd0) && (counter == 4'd0) && (state_reg == idle) && (wea == 1'b0)
    );

    ///// State encoding /////
    // State register only takes the defined encodings.
    check_state_encoding_valid: assert property (
        @(posedge clk) disable iff (reset)
            (state_reg inside {idle, leer, fin})
    );

    ///// State transitions /////
    // In IDLE with btn=0, stay in IDLE.
    check_idle_stay_when_btn0: assert property (
        @(posedge clk) disable iff (reset)
            (state_reg == idle && btn == 1'b0) |-> ##1 (reset || state_reg == idle)
    );
    // In IDLE with btn=1, go to LEER.
    check_idle_to_leer_when_btn1: assert property (
        @(posedge clk) disable iff (reset)
            (state_reg == idle && btn == 1'b1) |-> ##1 (reset || state_reg == leer)
    );
    // From LEER, next state is FIN.
    check_leer_to_fin: assert property (
        @(posedge clk) disable iff (reset)
            (state_reg == leer) |-> ##1 (reset || state_reg == fin)
    );
    // From FIN, next state is IDLE.
    check_fin_to_idle: assert property (
        @(posedge clk) disable iff (reset)
            (state_reg == fin) |-> ##1 (reset || state_reg == idle)
    );

    ///// WEA behavior /////
    // WEA is always 0 after reset.
    check_wea_const_zero: assert property (
        @(posedge clk) disable iff (reset)
            wea == 1'b0
    );

    ///// ADDRA behavior /////
    // ADDRA increments by 1 in FIN.
    check_addra_inc_in_fin: assert property (
        @(posedge clk) disable iff (reset)
            (state_reg == fin) |-> ##1 (reset || addra == $past(addra) + 1'b1)
    );
    // ADDRA holds in IDLE.
    check_addra_hold_in_idle: assert property (
        @(posedge clk) disable iff (reset)
            (state_reg == idle) |-> ##1 (reset || addra == $past(addra))
    );
    // ADDRA holds in LEER.
    check_addra_hold_in_leer: assert property (
        @(posedge clk) disable iff (reset)
            (state_reg == leer) |-> ##1 (reset || addra == $past(addra))
    );

    ///// COUNTER behavior /////
    // COUNTER increments by 1 in LEER.
    check_counter_inc_in_leer: assert property (
        @(posedge clk) disable iff (reset)
            (state_reg == leer) |-> ##1 (reset || counter == $past(counter) + 1'b1)
    );
    // COUNTER holds in IDLE.
    check_counter_hold_in_idle: assert property (
        @(posedge clk) disable iff (reset)
            (state_reg == idle) |-> ##1 (reset || counter == $past(counter))
    );
    // COUNTER resets to 0 in FIN when it equals 15.
    check_counter_reset_in_fin_at_15: assert property (
        @(posedge clk) disable iff (reset)
            (state_reg == fin && counter == 4'b1111) |-> ##1 (reset || counter == 4'd0)
    );
    // COUNTER holds in FIN when not 15.
    check_counter_hold_in_fin_not_15: assert property (
        @(posedge clk) disable iff (reset)
            (state_reg == fin && counter != 4'b1111) |-> ##1 (reset || counter == $past(counter))
    );
endmodule