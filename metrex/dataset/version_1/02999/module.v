module oh_clockmux #(parameter N    = 1)    (
    input [N-1:0] en, input [N-1:0] clkin,output 	  clkout 
    );

`ifdef CFG_ASIC
    generate
       if((N==2))
	 begin : asic
	    asic_clockmux2 imux (.clkin(clkin[N-1:0]),
				 .en(en[N-1:0]),
				 .clkout(clkout));
	 end
       else if((N==4))
	 begin : asic
	    asic_clockmux4 imux (.clkin(clkin[N-1:0]),
				 .en(en[N-1:0]),
				 .clkout(clkout));
	 end
    endgenerate
`else assign clkout = |(clkin[N-1:0] & en[N-1:0]);
`endif
       
endmodule 