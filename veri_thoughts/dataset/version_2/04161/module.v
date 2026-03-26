
module clock_gate_high_register_add_w31_0_2 (
    input CLK, 
    input EN, 
    input TE, 
    output reg ENCLK
);

  reg ECK;
  
  TLATNTSCAX2TS latch (
    .E(EN), 
    .SE(TE), 
    .CK(CLK), 
    .ECK(ECK)
  );
  
  always @ (*) begin
    ENCLK = ECK;
  end

endmodule
module TLATNTSCAX2TS (
    input E,
    input SE,
    input CK,
    output reg ECK
);

    always @(posedge CK or posedge SE) begin
        if (SE) begin
            // Scan enable is high, override the enable signal
            ECK <= 1'b1;
        end else begin
            // Scan enable is low, follow the enable signal
            ECK <= E;
        end
    end

endmodule