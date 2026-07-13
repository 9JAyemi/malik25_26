module mig_7series_v2_3_poc_edge_store_sva #(
    parameter int TCQ = 100,
    parameter int TAPCNTRWIDTH = 7,
    parameter int TAPSPERKCLK = 112
) (
    input  logic                         clk,
    input  logic                         run_polarity,
    input  logic                         run_end,
    input  logic                         select0,
    input  logic                         select1,
    input  logic [TAPCNTRWIDTH-1:0]      tap,
    input  logic [TAPCNTRWIDTH-1:0]      run,
    input  logic [TAPCNTRWIDTH-1:0]      fall_lead,
    input  logic [TAPCNTRWIDTH-1:0]      fall_trail,
    input  logic [TAPCNTRWIDTH-1:0]      rise_lead,
    input  logic [TAPCNTRWIDTH-1:0]      rise_trail
);

    // Low TAPSPERKCLK bits used by RTL in trailing_edge calc
    localparam logic [TAPCNTRWIDTH-1:0] TAPSPERKCLK_LSBS = TAPSPERKCLK[TAPCNTRWIDTH-1:0];

    // Helper to match RTL trailing_edge[TAPCNTRWIDTH-1:0]
    function automatic logic [TAPCNTRWIDTH-1:0] calc_te(
        input logic [TAPCNTRWIDTH-1:0] tap_i,
        input logic [TAPCNTRWIDTH-1:0] run_i
    );
        calc_te = (run_i > tap_i) ? (tap_i + TAPSPERKCLK_LSBS - run_i)
                                  : (tap_i - run_i);
    endfunction

    ///// Update on run_end with run_polarity == 1 /////
    // When run_end_this and run_polarity=1, fall_lead loads tap on next cycle.
    update_fall_lead_pospol: assert property (
        @(posedge clk) (run_end && select0 && select1 && run_polarity) |=> (fall_lead == $past(tap))
    );

    // When run_end_this and run_polarity=1, rise_trail loads trailing_edge LSBs on next cycle.
    update_rise_trail_pospol: assert property (
        @(posedge clk) (run_end && select0 && select1 && run_polarity) |=> (rise_trail == calc_te($past(tap), $past(run)))
    );

    // When run_end_this and run_polarity=1, rise_lead and fall_trail hold their previous values.
    hold_unaffected_pospol: assert property (
        @(posedge clk) (run_end && select0 && select1 && run_polarity) |=> (rise_lead == $past(rise_lead)) && (fall_trail == $past(fall_trail))
    );

    ///// Update on run_end with run_polarity == 0 /////
    // When run_end_this and run_polarity=0, rise_lead loads tap on next cycle.
    update_rise_lead_negpol: assert property (
        @(posedge clk) (run_end && select0 && select1 && ~run_polarity) |=> (rise_lead == $past(tap))
    );

    // When run_end_this and run_polarity=0, fall_trail loads trailing_edge LSBs on next cycle.
    update_fall_trail_negpol: assert property (
        @(posedge clk) (run_end && select0 && select1 && ~run_polarity) |=> (fall_trail == calc_te($past(tap), $past(run)))
    );

    // When run_end_this and run_polarity=0, fall_lead and rise_trail hold their previous values.
    hold_unaffected_negpol: assert property (
        @(posedge clk) (run_end && select0 && select1 && ~run_polarity) |=> (fall_lead == $past(fall_lead)) && (rise_trail == $past(rise_trail))
    );

    ///// Gating when run_end_this is false /////
    // If run_end_this is false, all outputs hold their values on next cycle.
    hold_when_no_update: assert property (
        @(posedge clk) !(run_end && select0 && select1) |=> (fall_lead == $past(fall_lead)) && (fall_trail == $past(fall_trail)) &&
                                                           (rise_lead == $past(rise_lead)) && (rise_trail == $past(rise_trail))
    );

endmodule