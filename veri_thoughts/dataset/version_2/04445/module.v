module SNPS_CLOCK_GATE_HIGH_d_ff_en_W32_0_6 ( CLK, EN, ENCLK, TE );
  input CLK, EN, TE;
  output ENCLK;

  TLATNTSCAX2TS latch ( .E(EN), .SE(TE), .CK(CLK), .ECK(ENCLK) );

endmodule

module TLATNTSCAX2TS (
    input E,      // Enable signal
    input SE,     // Scan enable (test enable)
    input CK,     // Clock input
    output reg ECK // Enabled clock output
);

    // Latch functionality
    always @(CK or E or SE) begin
        if (CK) begin
            if (SE) begin
                ECK <= 1'b1; // Force the clock high in test mode
            end else begin
                ECK <= E; // Normal mode: pass the clock based on enable
            end
        end
    end

endmodule
