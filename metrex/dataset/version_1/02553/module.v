module Synchro(dato, clk, ds);
input dato, clk;
output ds;

reg ds_reg;

always @(posedge clk) begin
    ds_reg <= dato;
end

assign ds = ds_reg;

endmodule

module Sincronizador(
    incambiarfuncion, incambiarsalida, inrst, inbtup, inbtdown, 
    outcambiarfuncion, outcambiarsalida, outrst, outbtup, outbtdown, clk
);
input incambiarfuncion, incambiarsalida, inrst, inbtup, inbtdown, clk;
output outcambiarfuncion, outcambiarsalida, outrst, outbtup, outbtdown;

Synchro S1 (
    .dato(incambiarfuncion), 
    .clk(clk), 
    .ds(outcambiarfuncion)
);
	 
Synchro S2 (
    .dato(incambiarsalida), 
    .clk(clk), 
    .ds(outcambiarsalida)
);
Synchro S3 (
    .dato(inrst), 
    .clk(clk), 
    .ds(outrst) 
);
Synchro S4 (
    .dato(inbtup), 
    .clk(clk), 
    .ds(outbtup)
);
Synchro S5 (
    .dato(inbtdown), 
    .clk(clk), 
    .ds(outbtdown)
);

endmodule