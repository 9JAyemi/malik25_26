
module pcie_7x_0_core_top_gtp_cpllpd_ovrd (                                                                                        
    input   i_ibufds_gte2,                                                                                     
    output  o_cpllpd_ovrd,                                                                                     
    output  o_cpllreset_ovrd                                                                                   
    );                                                                                                         
      reg [95:0] cpllpd_wait = 96'hFFFFFFFFFFFFFFFFFFFFFFFF;             
      reg [127:0] cpllreset_wait = 128'h000000000000000000000000000000FF;
    always @(posedge i_ibufds_gte2)                                                                            
    begin                                                                                                      
        cpllpd_wait <= {cpllpd_wait[94:0], 1'b0};                                                              
        cpllreset_wait <= {cpllreset_wait[126:0], 1'b0};                                                       
    end                                                                                                        
    assign o_cpllpd_ovrd = cpllpd_wait[95];                                                                    
    assign o_cpllreset_ovrd = cpllreset_wait[127];                                                             
endmodule
