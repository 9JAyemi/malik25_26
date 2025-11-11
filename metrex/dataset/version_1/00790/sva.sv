// SVA for radio_controller_TxTiming
module radio_controller_TxTiming_sva
(
    input clk,
    input reset,
    input Tx_swEnable,
    input [5:0] TxGain_target,
    input [3:0] TxGain_rampGainStep,
    input [3:0] TxGain_rampTimeStep,
    input [7:0] dly_hwTxEn,
    input [7:0] dly_TxStart,
    input [7:0] dly_PowerAmpEn,
    input [7:0] dly_RampGain,
    input hw_TxEn,
    input hw_TxStart,
    input hw_PAEn,
    input [5:0] hw_TxGain,

    // internals
    input [7:0] timing_counter,
    input [7:0] hwTxEn_counter,
    input [7:0] hwPAEn_counter,
    input [7:0] hwTxStart_counter,
    input [7:0] ramp_counter,
    input [6:0] TxGainBig,
    input [6:0] NewTxGain,
    input AutoGainRampEn
);

    default clocking cb @(posedge clk); endclocking
    default disable iff (reset);

    // Combinational equivalences
    assert property (hw_TxEn   == ((hwTxEn_counter   > dly_hwTxEn)    || (dly_hwTxEn    == 8'hFE)));
    assert property (hw_PAEn   == ((hwPAEn_counter   > dly_PowerAmpEn) || (dly_PowerAmpEn == 8'hFE)));
    assert property (hw_TxStart== ((hwTxStart_counter> dly_TxStart)    || (dly_TxStart   == 8'hFE)));
    assert property (AutoGainRampEn == (ramp_counter > dly_RampGain));
    assert property (NewTxGain == (((TxGainBig + TxGain_rampGainStep) > TxGain_target) ?
                                    TxGain_target : (TxGainBig + TxGain_rampGainStep)));
    assert property (hw_TxGain == TxGainBig[5:0]);

    // Clear on reset or disable
    assert property ((reset || !Tx_swEnable) |=> (TxGainBig==0
                                               && hwTxEn_counter==0
                                               && hwPAEn_counter==0
                                               && hwTxStart_counter==0
                                               && ramp_counter==0
                                               && timing_counter==0));

    // Counter increment/wrap rules
    assert property ((!reset && Tx_swEnable) |=> hwTxEn_counter    == (($past(hwTxEn_counter)    == 8'hFF) ? 8'h00 : $past(hwTxEn_counter)    + 8'h01));
    assert property ((!reset && Tx_swEnable) |=> hwPAEn_counter    == (($past(hwPAEn_counter)    == 8'hFF) ? 8'h00 : $past(hwPAEn_counter)    + 8'h01));
    assert property ((!reset && Tx_swEnable) |=> hwTxStart_counter == (($past(hwTxStart_counter) == 8'hFF) ? 8'h00 : $past(hwTxStart_counter) + 8'h01));
    assert property ((!reset && Tx_swEnable) |=> timing_counter    == (($past(timing_counter)    == 8'hFD) ? 8'h00 : $past(timing_counter)    + 8'h01));

    // Ramp counter/gain update behavior
    assert property ((!reset && Tx_swEnable && AutoGainRampEn)
                     |=> ramp_counter == (($past(ramp_counter) == TxGain_rampTimeStep) ? 8'h00
                                                                                       : $past(ramp_counter) + 8'h01));

    assert property ((!reset && Tx_swEnable && AutoGainRampEn && (ramp_counter == TxGain_rampTimeStep))
                     |=> TxGainBig == (( $past(TxGainBig) + TxGain_rampGainStep) > TxGain_target
                                        ? TxGain_target
                                        : ($past(TxGainBig) + TxGain_rampGainStep)));

    assert property ((!reset && Tx_swEnable && AutoGainRampEn && (ramp_counter != TxGain_rampTimeStep))
                     |=> $stable(TxGainBig));

    assert property ((!reset && Tx_swEnable && !AutoGainRampEn)
                     |=> $stable(ramp_counter) && $stable(TxGainBig));

    // Monotonic non-decreasing gain when enabled
    assert property ((!reset && Tx_swEnable && $past(!reset && Tx_swEnable))
                     |-> (TxGainBig >= $past(TxGainBig)));

    // Delay edge-cases
    assert property ((dly_hwTxEn    == 8'hFF) |-> !hw_TxEn);
    assert property ((dly_PowerAmpEn== 8'hFF) |-> !hw_PAEn);
    assert property ((dly_TxStart   == 8'hFF) |-> !hw_TxStart);

    // X-checks on primary outputs
    assert property (!$isunknown({hw_TxEn, hw_PAEn, hw_TxStart, hw_TxGain}));

    // Coverage
    cover property (!reset && Tx_swEnable && (dly_hwTxEn!=8'hFE) && (dly_hwTxEn!=8'hFF) ##1 $rose(hw_TxEn));
    cover property (!reset && (dly_hwTxEn==8'hFE) && hw_TxEn);
    cover property (!reset && Tx_swEnable && (hwTxEn_counter==8'hFF) ##1 (hwTxEn_counter==8'h00));
    cover property (!reset && Tx_swEnable && (hwPAEn_counter==8'hFF) ##1 (hwPAEn_counter==8'h00));
    cover property (!reset && Tx_swEnable && (hwTxStart_counter==8'hFF) ##1 (hwTxStart_counter==8'h00));
    cover property (!reset && Tx_swEnable && (timing_counter==8'hFD) ##1 (timing_counter==8'h00));

    cover property (!reset && Tx_swEnable && AutoGainRampEn
                    && (ramp_counter==TxGain_rampTimeStep) && (TxGainBig != TxGain_target)
                    ##1 (TxGainBig > $past(TxGainBig)));

    cover property (!reset && Tx_swEnable && AutoGainRampEn
                    && (ramp_counter==TxGain_rampTimeStep)
                    && (($past(TxGainBig)+TxGain_rampGainStep) > TxGain_target)
                    ##1 (TxGainBig == TxGain_target));

endmodule

// Bind into DUT (allows access to internals by name)
bind radio_controller_TxTiming radio_controller_TxTiming_sva sva_inst (.*);