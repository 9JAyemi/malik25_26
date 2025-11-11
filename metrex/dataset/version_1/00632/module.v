module red_pitaya_lpf_block
#(
    parameter     SHIFTBITS =     4,
    parameter     SIGNALBITS   = 14,
    parameter     MINBW        = 10
    )
(
    input clk_i,
    input rstn_i  ,
    input [SHIFTBITS:0] shift, 
    input filter_on,
    input highpass,
    input signed  [SIGNALBITS-1:0] signal_i,
    output signed [SIGNALBITS-1:0] signal_o
);

localparam MAXSHIFT = $clog2(125000000/MINBW);

reg signed [SIGNALBITS+MAXSHIFT-1:0] y;
reg signed [SIGNALBITS+MAXSHIFT-1:0] delta;
wire signed [SIGNALBITS+MAXSHIFT-1:0] shifted_delta;
wire signed [SIGNALBITS-1:0] y_out;
wire filter_off;

assign y_out = y[MAXSHIFT+SIGNALBITS-1:MAXSHIFT];
assign shifted_delta = delta<<((shift<MAXSHIFT) ? shift : MAXSHIFT);

always @(posedge clk_i) begin
    if (rstn_i == 1'b0) begin
        y <= {MAXSHIFT+SIGNALBITS{1'b0}};
        delta <= {MAXSHIFT+SIGNALBITS{1'b0}};
    end
    else begin
        delta <= signal_i - y_out;
        y <= y + shifted_delta;
    end
end
  
assign signal_o = (filter_on == 1'b0) ? signal_i : ((highpass==1'b0) ? y_out : delta);

endmodule