module clock_gate_high_sva (
    input logic CLK,
    input logic EN,
    input logic TE,
    output logic ENCLK
);
    // Ensure ENCLK is LOW when SE is HIGH
    property p_se_high;
        @(posedge CLK) disable iff (!EN) TE |-> !ENCLK;
    endproperty
    assert property (p_se_high) else $error("ENCLK should be LOW when SE is HIGH");

    // Ensure ENCLK is HIGH when SE is LOW and EN is HIGH
    property p_se_low_en_high;
        @(posedge CLK) disable iff (!EN) !TE && EN |-> ENCLK;
    endproperty
    assert property (p_se_low_en_high) else $error("ENCLK should be HIGH when SE is LOW and EN is HIGH");

    // Ensure ENCLK is LOW when SE is LOW and EN is LOW
    property p_se_low_en_low;
        @(posedge CLK) disable iff (!EN) !TE && !EN |-> !ENCLK;
    endproperty
    assert property (p_se_low_en_low) else $error("ENCLK should be LOW when SE is LOW and EN is LOW");

endmodule