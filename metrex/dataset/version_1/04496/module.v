
module mgc_out_reg_pos (clk, en, arst, srst, ld, d, lz, z);

    parameter integer rscid   = 1;
    parameter integer width   = 8;
    parameter         ph_en   =  1'b1;
    parameter         ph_arst =  1'b0;
    parameter         ph_srst =  1'b0;

    input              clk;
    input              en;
    input              arst;
    input              srst;
    input              ld;
    input  [width-1:0] d;
    output             lz;
    output [width-1:0] z;


    reg  lz_r;
    reg  [width-1:0] z_r;
    reg  lz_r_dly;
    reg [width-1:0] z;

       initial begin
          lz_r = 1'b0;
          z_r  = {width{1'b0}};
          lz_r_dly = 1'b0;
       end

    always @(posedge clk)
    begin
        if (arst == ph_arst)
        begin
            lz_r   <= 1'b0;
            z_r    <= {width{1'b0}};
            //lz_r_dly <= 1'b0;
        end
        else
        begin
            lz_r   <= (en == ph_en) ? ld  : lz_r;
            z_r    <= (en == ph_en) ? d  : z_r;
            //lz_r_dly <= lz_r; 
        end
    end


    always @(posedge clk )
    begin
        if (srst == ph_srst)
        begin
            z <= {width{1'b0}};
        end
        else
        begin
            z <= lz_r_dly ? {width{1'b0}} : z_r;
        end
    end

    assign lz = lz_r;

endmodule