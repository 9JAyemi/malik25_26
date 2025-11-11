


module shift_reg #(
    parameter REG_SZ = 93,
    parameter FEED_FWD_IDX = 65,
    parameter FEED_BKWD_IDX = 68
) 
(
    
    input   wire            clk_i,      
    input   wire            n_rst_i,    
    input   wire            ce_i,       
      
   
    input   wire    [2:0]   ld_i,       
    input   wire    [31:0]  ld_dat_i,   
    input   wire            dat_i,      
    output  wire            dat_o,      
    output  wire            z_o         
);

reg     [(REG_SZ - 1):0]    dat_r;      
wire                        reg_in_s;   

assign reg_in_s = dat_i ^ dat_r[FEED_BKWD_IDX];

always @(posedge clk_i or negedge n_rst_i) begin
    if (!n_rst_i)
        dat_r <= 0;
    else begin
        if (ce_i) begin
            
            dat_r <= {dat_r[(REG_SZ - 2):0], reg_in_s};
        end
        else if (ld_i != 3'b000) begin 
            if (ld_i[0])
                dat_r[31:0] <= ld_dat_i;
            else if (ld_i[1])
                dat_r[63:32] <= ld_dat_i;
            else if (ld_i[2])
                dat_r[79:64] <= ld_dat_i[15:0];
         
               
            dat_r[(REG_SZ - 1):80] <= 0;
            if (REG_SZ == 111)
                dat_r[(REG_SZ - 1)-:3] <= 3'b111;
        end
    end
end

assign z_o = (dat_r[REG_SZ - 1] ^ dat_r[FEED_FWD_IDX]);
assign dat_o = z_o ^ (dat_r[REG_SZ - 2] & dat_r[REG_SZ - 3]); 

endmodule
