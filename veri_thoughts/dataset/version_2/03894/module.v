module DFF_with_CLR_E(input D, C, E, CLR, output Q);
    wire CLR_bar;
    assign CLR_bar = ~CLR;
    DFFNE _TECHMAP_REPLACE_ (.D(D), .Q(Q), .CLK(C), .CE(~E), .CLR(CLR_bar));
endmodule

module DFFNE(D, Q, CLK, CE, CLR);
    input D, CLK, CE, CLR;
    output reg Q;

    always @(posedge CLK or negedge CLR)
    begin
        if (~CLR)
            Q <= 1'b0;
        else if (CE)
            Q <= D;
    end
endmodule