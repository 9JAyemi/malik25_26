


module red_pitaya_iq_hpf_block #(
    parameter     ALPHABITS = 25,
    parameter     HIGHESTALPHABIT = 18,
    parameter     LPFBITS   = 14
)
(
    input clk_i,
    input reset_i  ,
    input signed [HIGHESTALPHABIT-1:0] alpha_i, 

    input signed [LPFBITS-1:0] signal_i,
    output signed [LPFBITS-1:0] signal_o
);

reg  signed [LPFBITS+ALPHABITS-1:0]    y;
reg  signed [LPFBITS+ALPHABITS-1:0]    delta;   wire signed [LPFBITS+1-1:0] diff;
reg  signed [LPFBITS-1:0]  delta_out;
wire signed [LPFBITS-1:0]  y_out;

assign y_out = y[ALPHABITS+LPFBITS-1:ALPHABITS];
assign diff = signal_i-y_out;  

always @(posedge clk_i) begin
if (reset_i == 1'b1) begin
        y <=            {ALPHABITS+LPFBITS{1'b0}};
        delta <=        {ALPHABITS+LPFBITS{1'b0}};
        delta_out <=    {LPFBITS{1'b0}};
    end
    else begin
        delta <= diff * alpha_i;
        y <= y + delta;
        if (diff[LPFBITS:LPFBITS-1] == 2'b01)
            delta_out <= {1'b0,{LPFBITS-1{1'b1}}};
        else if (diff[LPFBITS:LPFBITS-1] == 2'b10)
            delta_out <= {1'b1,{LPFBITS-1{1'b0}}};
        else
            delta_out <= diff[LPFBITS-1:0];
    end
end

assign signal_o = delta_out;

endmodule
