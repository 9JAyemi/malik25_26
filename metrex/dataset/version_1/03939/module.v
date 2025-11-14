module LCD_control(
    input [7:0] iRed,
    input [7:0] iGreen,
    input [7:0] iBlue,
    output [9:0] oCurrent_X,    output [9:0] oCurrent_Y,    output [21:0] oAddress,     output oRequest,            output reg oTopOfScreen,    output [7:0] oLCD_R,
    output [7:0] oLCD_G,
    output [7:0] oLCD_B,
    output reg oLCD_HS,   output reg oLCD_VS,   output oLCD_DE,   input iCLK,
    input iRST_N
);

reg         [10:0]  H_Cont;
reg         [10:0]  V_Cont;
parameter   H_FRONT =   24;
parameter   H_SYNC  =   72;
parameter   H_BACK  =   96;
parameter   H_ACT   =   800;
parameter   H_BLANK =   H_FRONT+H_SYNC+H_BACK;
parameter   H_TOTAL =   H_FRONT+H_SYNC+H_BACK+H_ACT;
parameter   V_FRONT =   3;
parameter   V_SYNC  =   10;
parameter   V_BACK  =   7;
parameter   V_ACT   =   480;
parameter   V_BLANK =   V_FRONT+V_SYNC+V_BACK;
parameter   V_TOTAL =   V_FRONT+V_SYNC+V_BACK+V_ACT;
assign  oLCD_R      =   oRequest ? iRed : 8'b0 ;
assign  oLCD_G      =   oRequest ? iGreen : 8'b0 ;
assign  oLCD_B      =   oRequest ? iBlue : 8'b0 ;
assign  oAddress    =   oCurrent_Y*H_ACT + oCurrent_X;
assign  oRequest    =   H_Cont >= H_BLANK && V_Cont >= V_BLANK;
assign  oCurrent_X  =   (H_Cont>=H_BLANK) ? H_Cont-H_BLANK : 11'h0;
assign  oCurrent_Y  =   (V_Cont>=V_BLANK) ? V_Cont-V_BLANK : 11'h0;
assign  oLCD_DE     =   oRequest;


wire oTopOfScreenNext = H_Cont == 0 && V_Cont == 0;
always @(posedge iCLK)
begin
    oTopOfScreen <= oTopOfScreenNext;
end

always @(posedge iCLK or negedge iRST_N)
begin
    if (!iRST_N) begin
        H_Cont <= 0;
        oLCD_HS <= 1;
    end else begin
        if (H_Cont < H_TOTAL - 1) begin
            H_Cont <= H_Cont + 1'b1;
        end else begin
            H_Cont <= 0;
        end

        if (H_Cont == H_FRONT - 1) begin
            oLCD_HS <= 1'b0;
        end
        if (H_Cont == H_FRONT + H_SYNC - 1) begin
            oLCD_HS <= 1'b1;
        end
    end
end

always @(posedge iCLK or negedge iRST_N)
begin
    if (!iRST_N) begin
        V_Cont <= 0;
        oLCD_VS <= 1;
    end else if (H_Cont == 0) begin
        if (V_Cont < V_TOTAL-1) begin
            V_Cont <= V_Cont+1'b1;
        end else begin
            V_Cont <= 0;
        end

        if (V_Cont == V_FRONT - 1) begin
            oLCD_VS <= 1'b0;
        end
        if (V_Cont == V_FRONT + V_SYNC - 1) begin
            oLCD_VS <= 1'b1;
        end
    end
end

endmodule
