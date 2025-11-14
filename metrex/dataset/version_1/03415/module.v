
module Reset_Delay(iRST,iCLK,oRESET);
input iCLK;
input iRST;
output reg oRESET;
reg [27:0] Cont;
always@(posedge iCLK or negedge iRST)
begin
    if(!iRST)
    begin
        oRESET <= 1'b0;
        Cont <= 28'b0;
    end
    else
    begin
        Cont <= Cont + 1'b1;
        if(Cont != 28'h4FFFFFF) // about 300ms at 50MHz
            oRESET <= 1'b1;
    end
end
endmodule