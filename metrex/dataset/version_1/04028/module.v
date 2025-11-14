

module vgabase(
    input wire clk,
    input wire clr,
    output reg hsync,
    output reg vsync,
    output reg [11:0] hc,
    output reg [11:0] vc,
    output wire vidon
  );


parameter hpixels = 12'd1344;
parameter vlines  = 12'd806;
parameter hsp   = 12'd136;
parameter hbp   = 12'd160;
parameter hfp   = 12'd24;
parameter vsp   = 12'd6;
parameter vbp   = 12'd29;
parameter vfp   = 12'd3;


reg vsenable;

initial begin
  hc <= hpixels - hsp - hbp;
  vc <= vlines - vsp - vbp;
  hsync <= 0;
  vsync <= 0;
  vsenable <= 0;
end

always @(posedge clk or posedge clr) begin
    if(clr == 1)
      hc <= hpixels - hsp - hbp;
  else begin
      if(hc == hpixels - 1) begin
        hc <= 0;
      vsenable <= 1;
    end else begin
        hc <= hc + 1'b1;
      vsenable <= 0;
    end
  end
end

always @(*) begin
    if(hpixels - hsp - hbp < hc && hc <= hpixels - hbp)
      hsync = 0;
  else
      hsync = 1;
end

always @(posedge clk or posedge clr) begin
    if(clr == 1)
      vc <= vlines - vsp - vbp;
  else if(vsenable == 1)
      if(vc == vlines - 1)
        vc <= 0;
    else
        vc <= vc + 1'b1;
end

always @(*) begin
    if(vlines - vsp - vbp < vc && vc <= vlines - vbp)
      vsync = 0;
  else
      vsync = 1;
end

assign vidon=(hc<hpixels-hfp-hsp-hbp)&&(vc<vlines-vfp-vsp-vbp);

endmodule
