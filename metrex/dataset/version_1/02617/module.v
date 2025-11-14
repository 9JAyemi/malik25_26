module cross_domain_sync (
    input capturetrig1, // input trigger signal from other clock domain
    input  read_Mux_In, // input data signal from other clock domain
    input s_axi_aclk, // local clock signal
    output reg captureTrig1_d0 // synchronized output data signal
);

  // Declare internal wires
  wire CaptureTrig1_int;
  wire s_level_out_d1_cdc_to;
  wire s_level_out_d2;
  wire s_level_out_d3;

  // Instantiate FDRE primitive components for cross-domain synchronization
  FDRE GENERATE_LEVEL_P_S_CDC_SINGLE_BIT_CROSS_PLEVEL_IN2SCNDRY_IN_cdc_to 
       (.C(s_axi_aclk),
        .CE(1'b1),
        .D(capturetrig1),
        .Q(s_level_out_d1_cdc_to),
        .R(1'b0));
  FDRE GENERATE_LEVEL_P_S_CDC_SINGLE_BIT_CROSS_PLEVEL_IN2SCNDRY_s_level_out_d2 
       (.C(s_axi_aclk),
        .CE(1'b1),
        .D(s_level_out_d1_cdc_to),
        .Q(s_level_out_d2),
        .R(1'b0));
  FDRE GENERATE_LEVEL_P_S_CDC_SINGLE_BIT_CROSS_PLEVEL_IN2SCNDRY_s_level_out_d3 
       (.C(s_axi_aclk),
        .CE(1'b1),
        .D(s_level_out_d2),
        .Q(s_level_out_d3),
        .R(1'b0));
  FDRE GENERATE_LEVEL_P_S_CDC_SINGLE_BIT_CROSS_PLEVEL_IN2SCNDRY_s_level_out_d4 
       (.C(s_axi_aclk),
        .CE(1'b1),
        .D(s_level_out_d3),
        .Q(CaptureTrig1_int),
        .R(1'b0));


  always @(posedge s_axi_aclk) begin
    if (CaptureTrig1_int) begin
      captureTrig1_d0 <= read_Mux_In;
    end
  end


endmodule

module FDRE(
    input D,     
    input C,    
    input CE,    
    input R,     
    output reg Q 
);

always @(posedge C) begin
    if (R) begin
        Q <= 1'b0; 
    end
    else if (CE) begin
        Q <= D; 
    end
end

endmodule
