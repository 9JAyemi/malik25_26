
module XORCY (O, CI, LI);


`ifdef XIL_TIMING

    parameter LOC = "UNPLACED";

`endif

    
    output O;

    input  CI, LI;

	xor X1 (O, CI, LI);

`ifdef XIL_TIMING

    specify
        
        (CI => O) = (0:0:0, 0:0:0);
        (LI => O) = (0:0:0, 0:0:0);
        specparam PATHPULSE$ = 0;
        
    endspecify

`endif
    
endmodule
