module radio_controller_TxTiming
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
    output hw_TxEn,
    output hw_TxStart,
    output hw_PAEn,
    output [5:0] hw_TxGain
);

    reg [7:0] timing_counter;
    reg [7:0] hwTxEn_counter;
    reg [7:0] hwPAEn_counter;
    reg [7:0] hwTxStart_counter;
    reg [7:0] ramp_counter;
    reg [6:0] TxGainBig;
    wire [6:0] NewTxGain;
    wire AutoGainRampEn;

    assign NewTxGain = (TxGainBig + TxGain_rampGainStep > TxGain_target) ? TxGain_target : TxGainBig + TxGain_rampGainStep;
    assign hw_TxGain = TxGainBig[5:0];

    assign hw_TxEn = (hwTxEn_counter > dly_hwTxEn) || (dly_hwTxEn == 8'hFE);
    assign hw_PAEn = (hwPAEn_counter > dly_PowerAmpEn) || (dly_PowerAmpEn == 8'hFE);
    assign hw_TxStart = (hwTxStart_counter > dly_TxStart) || (dly_TxStart == 8'hFE);

    assign AutoGainRampEn = ramp_counter > dly_RampGain;

    always @(posedge clk) begin
        if (reset || !Tx_swEnable) begin
            TxGainBig <= 0;
            hwTxEn_counter <= 0;
            hwPAEn_counter <= 0;
            hwTxStart_counter <= 0;
            ramp_counter <= 0;
        end else begin
            if (hwTxEn_counter == 8'hFF) begin
                hwTxEn_counter <= 0;
            end else begin
                hwTxEn_counter <= hwTxEn_counter + 1;
            end
            if (hwPAEn_counter == 8'hFF) begin
                hwPAEn_counter <= 0;
            end else begin
                hwPAEn_counter <= hwPAEn_counter + 1;
            end
            if (hwTxStart_counter == 8'hFF) begin
                hwTxStart_counter <= 0;
            end else begin
                hwTxStart_counter <= hwTxStart_counter + 1;
            end
            if (AutoGainRampEn) begin
                if (ramp_counter == TxGain_rampTimeStep) begin
                    TxGainBig <= NewTxGain;
                    ramp_counter <= 0;
                end else begin
                    ramp_counter <= ramp_counter + 1;
                end
            end
        end
    end

    always @(posedge clk) begin
        if (reset || !Tx_swEnable) begin
            timing_counter <= 0;
        end else begin
            if (timing_counter == 8'hFD) begin
                timing_counter <= 0;
            end else begin
                timing_counter <= timing_counter + 1;
            end
        end
    end

endmodule