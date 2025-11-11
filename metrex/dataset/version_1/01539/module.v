

module jt10_adpcm_comb(
    input           rst_n,
    input           clk,        input           cen,        input   [3:0]   data,
    input           chon,       output signed [15:0] pcm
);

localparam stepw = 15;

reg signed [15:0] x1, x2, x3, x4, x5, x6;
reg [stepw-1:0] step1, step2, step6;
reg [stepw+1:0] step3, step4, step5;
assign pcm = x2;

reg  [18:0] d2l;
reg  [15:0] d3,d4;
reg  [3:0]  d1,d2;
reg         sign2, sign3, sign4, sign5;
reg  [7:0]  step_val;
reg  [22:0] step2l;

reg chon2, chon3, chon4, chon5;
reg signEqu4, signEqu5;
reg [3:0] data1,data2;

always @( * )
    if( ! rst_n ) begin
        x2 = 'd0; step2 = 'd127;
        x3 = 'd0; step3 = 'd127;
        x4 = 'd0; step4 = 'd127;
        x5 = 'd0; step5 = 'd127;
        x6 = 'd0; step6 = 'd127;
        d2 = 'd0; d3 = 'd0; d4 = 'd0;
        sign2 = 'b0;
        sign3 = 'b0;
        sign4 = 'b0; sign5 = 'b0;
        chon2 = 'b0;   chon3 = 'b0;   chon4 = 'b0; chon5 = 1'b0;
    end else begin
        d2        = d1;
        sign2     = data1[3];
        data2     = data1;
        x2        = x1;
        step2     = step1;
        chon2     = chon;
        casez( d2[3:1] )
            3'b0_??: step_val = 8'd57;
            3'b1_00: step_val = 8'd77;
            3'b1_01: step_val = 8'd102;
            3'b1_10: step_val = 8'd128;
            3'b1_11: step_val = 8'd153;
        endcase d2l    = d2 * step2; step2l = step_val * step2; d3        = d2l[18:3]; sign3     = sign2;
        x3        = x2;
        step3     = step2l[22:6];
        chon3     = chon2;
        d4        = sign3 ? ~d3+16'b1 : d3;
        sign4     = sign3;
        signEqu4  = sign3 == x3[15];
        x4        = x3;
        step4     = step3;
        chon4     = chon3;
        x5        = x4+d4;
        sign5     = sign4;
        signEqu5  = signEqu4;
        step5     = step4;
        chon5     = chon4;
        if( chon5 ) begin
            if( signEqu5 && (sign5!=x5[15]) )
                x6 = sign5 ? 16'h8000 : 16'h7FFF;
            else
                x6 = x5;

            if( step5 < 127 )
                step6  = 15'd127;
            else if( step5 > 24576 )
                step6  = 15'd24576;
            else
                step6 = step5[14:0];
        end else begin
            x6      = 'd0;
            step6   = 'd127;
        end
    end

always @(posedge clk or negedge rst_n) 
    if( ! rst_n ) begin
        x1 <= 'd0; step1 <= 'd127; 
        d1 <= 'd0; data1 <= 'd0;
    end else if(cen) begin
        d1    <= {data[2:0],1'b1};
        x1    <= x6;
        step1 <= step6;
        data1 <= data;
    end

endmodule // jt10_adpcm    