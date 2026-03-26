module SSCG_sva #(
    parameter logic [31:0] f_nom    = 32'd10000,
    parameter logic [31:0] f_delta  = 32'd100,
    parameter logic [31:0] f_spread = 32'd1000,
    parameter logic [31:0] clk_div  = 32'd10
) (
    input logic        ref_clk,
    input logic        modulation,
    input logic        ssc_clk,
    input logic [31:0] counter,
    input logic [31:0] mod_counter,
    input logic [31:0] delta_counter,
    input logic [31:0] delta,
    input logic [31:0] ssc_clk_counter,
    input logic [31:0] mod_signal,
    input logic [31:0] delta_signal
);

    localparam logic [31:0] HALF_F_SPREAD = f_spread / 32'd2;
    localparam logic [31:0] HALF_F_NOM    = f_nom / 32'd2;

    // mod_signal follows the RTL's piecewise definition.
    check_mod_signal_definition: assert property (
        @(posedge ref_clk)
        mod_signal == ((mod_counter < HALF_F_SPREAD) ? mod_counter : (f_spread - mod_counter))
    );

    // ssc_clk reflects the current ssc_clk_counter threshold.
    check_ssc_clk_definition: assert property (
        @(posedge ref_clk)
        ssc_clk == ((ssc_clk_counter < HALF_F_NOM) ? 1'b0 : 1'b1)
    );

    // counter increments when the divider terminal count is not reached.
    check_counter_increments_between_divisions: assert property (
        @(posedge ref_clk)
        (counter != (clk_div - 32'd1)) |=> (counter == ($past(counter) + 32'd1))
    );

    // counter clears when the divider terminal count is reached.
    check_counter_resets_on_division: assert property (
        @(posedge ref_clk)
        (counter == (clk_div - 32'd1)) |=> (counter == 32'd0)
    );

    // Other state holds when counter is not at the divider terminal count.
    check_state_holds_when_counter_not_terminal: assert property (
        @(posedge ref_clk)
        (counter != (clk_div - 32'd1)) |=> (
            (mod_counter     == $past(mod_counter))     &&
            (delta_counter   == $past(delta_counter))   &&
            (delta           == $past(delta))           &&
            (ssc_clk_counter == $past(ssc_clk_counter))
        )
    );

    // mod_counter increments on divider terminal counts before wrap.
    check_mod_counter_increments_on_division: assert property (
        @(posedge ref_clk)
        ((counter == (clk_div - 32'd1)) && (mod_counter != f_spread)) |=> (
            mod_counter == ($past(mod_counter) + 32'd1)
        )
    );

    // mod_counter wraps to zero when it equals f_spread.
    check_mod_counter_wraps_at_spread: assert property (
        @(posedge ref_clk)
        ((counter == (clk_div - 32'd1)) && (mod_counter == f_spread)) |=> (
            mod_counter == 32'd0
        )
    );

    // delta_counter increments on divider terminal counts until match.
    check_delta_counter_increments_until_match: assert property (
        @(posedge ref_clk)
        ((counter == (clk_div - 32'd1)) && (delta_counter != delta_signal)) |=> (
            delta_counter == ($past(delta_counter) + 32'd1)
        )
    );

    // delta_counter clears when it matches delta_signal.
    check_delta_counter_resets_on_match: assert property (
        @(posedge ref_clk)
        ((counter == (clk_div - 32'd1)) && (delta_counter == delta_signal)) |=> (
            delta_counter == 32'd0
        )
    );

    // delta increments by f_delta on a delta_counter match.
    check_delta_updates_on_match: assert property (
        @(posedge ref_clk)
        ((counter == (clk_div - 32'd1)) && (delta_counter == delta_signal)) |=> (
            delta == ($past(delta) + f_delta)
        )
    );

    // delta holds on divider terminal counts without a delta_counter match.
    check_delta_holds_without_match_on_division: assert property (
        @(posedge ref_clk)
        ((counter == (clk_div - 32'd1)) && (delta_counter != delta_signal)) |=> (
            delta == $past(delta)
        )
    );

    // ssc_clk_counter increments on divider terminal counts before wrap.
    check_ssc_clk_counter_increments_on_division: assert property (
        @(posedge ref_clk)
        ((counter == (clk_div - 32'd1)) && (ssc_clk_counter != f_nom)) |=> (
            ssc_clk_counter == ($past(ssc_clk_counter) + 32'd1)
        )
    );

    // ssc_clk_counter wraps to zero when it equals f_nom.
    check_ssc_clk_counter_wraps_at_nominal_period: assert property (
        @(posedge ref_clk)
        ((counter == (clk_div - 32'd1)) && (ssc_clk_counter == f_nom)) |=> (
            ssc_clk_counter == 32'd0
        )
    );

endmodule