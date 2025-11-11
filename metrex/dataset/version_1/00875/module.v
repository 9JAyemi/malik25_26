module asram16_if 
(
    clk_i, 
    rst_i, 
    timing_ctrl_i,
    
    sram_address_o, 
    sram_data_o, 
    sram_data_i, 
    sram_oe_o, 
    sram_cs_o, 
    sram_be_o, 
    sram_we_o, 
    sram_dir_out_o, 
    
    address_i, 
    data_i, 
    data_o, 
    rd_i, 
    wr_i, 
    ack_o, 
    busy_o 
);

parameter  [31:0]       EXT_ADDR_WIDTH = 17;
    
input                   clk_i ;
input                   rst_i ;
input [(32 - 1):0]      timing_ctrl_i ;
output [(EXT_ADDR_WIDTH - 1):0]  sram_address_o ;
output [(16 - 1):0]     sram_data_o ;
input [(16 - 1):0]      sram_data_i ;
output                  sram_oe_o ;
output                  sram_cs_o ;
output [(2 - 1):0]      sram_be_o ;
output                  sram_we_o ;
output                  sram_dir_out_o ;
input [(32 - 1):0]      address_i ;
input [(32 - 1):0]      data_i ;
output [(32 - 1):0]     data_o ;
input                   rd_i ;
input [(4 - 1):0]       wr_i ;
output                  ack_o ;
output                  busy_o ;

reg [3:0]                reg_state;
parameter MEM_IDLE          = 4'd0;
parameter MEM_WRITE_DATA1   = 4'd1;
parameter MEM_WRITE_SETUP2  = 4'd2;
parameter MEM_WRITE_DATA2   = 4'd3;
parameter MEM_READ_DATA1    = 4'd4;
parameter MEM_READ_DATA2    = 4'd5;
parameter MEM_READ_WAIT1    = 4'd6;
parameter MEM_READ_WAIT2    = 4'd7;
parameter MEM_WRITE_WAIT1   = 4'd8;
parameter MEM_WRITE_WAIT2   = 4'd9;
parameter MEM_WRITE_HOLD    = 4'd10;

reg [(EXT_ADDR_WIDTH - 1):0] v_reg_address;
reg [(EXT_ADDR_WIDTH - 1):0] reg_address;
reg [(32 - 1):0]             reg_data_o;
reg [(32 - 1):0]             reg_data_i;
reg [(4 - 1):0]              reg_wr;
reg [3:0]                    reg_wait;
reg [(EXT_ADDR_WIDTH - 1):0] sram_address_o;
reg [(16 - 1):0]             sram_data_o;
reg                          sram_oe_o;
wire                         sram_cs_o;
reg [(2 - 1):0]              sram_be_o;
reg                          sram_we_o;
reg                          sram_dir_out_o;
wire [(32 - 1):0]            data_o;
reg                          ack_o;
wire                         busy_o;

always @ (posedge clk_i or posedge rst_i )
begin 
   if (rst_i == 1'b1)
   begin 
       sram_oe_o        <= 1'b1;
       sram_we_o        <= 1'b1;
       sram_address_o   <= {(EXT_ADDR_WIDTH - 0){1'b0}};
       sram_data_o      <= 16'h0000;
       sram_be_o        <= 2'b11;
       sram_dir_out_o   <= 1'b1;
       
       ack_o            <= 1'b0;
       
       reg_address      <= {(EXT_ADDR_WIDTH - 0){1'b0}};
       reg_data_o       <= 32'h00000000;
       reg_data_i       <= 32'h00000000;
       reg_wr           <= 4'b0000;
       reg_wait         <= 4'b0000;
       reg_state        <= MEM_IDLE;       
   end
   else 
   begin 
   
       ack_o <= 1'b0;
       
       case (reg_state)
       
       MEM_IDLE : 
       begin

           v_reg_address = address_i[EXT_ADDR_WIDTH:1];
           
           if (wr_i != 4'b0000) 
           begin
           
               reg_address  <= v_reg_address;
               reg_data_o   <= data_i;
               reg_data_i   <= 32'h00000000;
               reg_wr       <= wr_i;
               
               sram_dir_out_o    <= 1'b1;
               
               if (wr_i[3:2] != 2'b00)
               begin
                   sram_address_o   <= v_reg_address;
                   sram_data_o      <= data_i[31:16];
                   sram_be_o        <= ~wr_i[3:2];
                   sram_we_o        <= 1'b0;
                   
                   if (timing_ctrl_i[3:0] != 4'b0000)
                   begin
                        reg_wait    <= timing_ctrl_i[3:0];
                        reg_state   <= MEM_WRITE_WAIT1;
                   end
                   else
                        reg_state   <= MEM_WRITE_DATA1;
               end
               else 
               begin 
                   sram_address_o   <= (v_reg_address + 1);
                   sram_data_o      <= data_i[15:0];
                   sram_be_o        <= ~wr_i[1:0];
                   sram_we_o        <= 1'b0;

                   if (timing_ctrl_i[3:0] != 4'b0000)
                   begin
                        reg_wait    <= timing_ctrl_i[3:0];
                        reg_state   <= MEM_WRITE_WAIT2;
                   end
                   else
                        reg_state   <= MEM_WRITE_DATA2;
               end
           end
           else if (rd_i == 1'b1)
           begin
           
               reg_address      <= v_reg_address;
               reg_data_o       <= 32'h00000000;
               reg_data_i       <= 32'h00000000;
               reg_wr           <= 4'b0000;
               
               sram_address_o   <= v_reg_address;
               sram_data_o      <= 16'h0000;
               sram_be_o        <= 2'b00;
               sram_we_o        <= 1'b1;
               sram_oe_o        <= 1'b0;
               sram_dir_out_o   <= 1'b0;
               
               if (timing_ctrl_i[7:4] != 4'b0000)
               begin
                    reg_wait    <= timing_ctrl_i[7:4];
                    reg_state   <= MEM_READ_WAIT1;
               end
               else
                    reg_state   <= MEM_READ_DATA1;
           end
           else 
           begin 
               sram_dir_out_o   <= 1'b1;
               reg_state        <= MEM_IDLE;
           end
       end
       MEM_WRITE_DATA1 : 
       begin
           sram_we_o    <= 1'b1;
           
           reg_address    <= (reg_address + 1);
           
           if (reg_wr[1:0]!=2'b00)
           begin

               if (timing_ctrl_i[11:8] != 4'b0000)
               begin
                    reg_wait    <= timing_ctrl_i[11:8];
                    reg_state   <= MEM_WRITE_HOLD;
               end
               else
                    reg_state   <= MEM_WRITE_SETUP2;
           end
           else 
           begin 
               reg_state    <= MEM_IDLE;
               ack_o        <= 1'b1;
           end
       end
       MEM_WRITE_SETUP2 : 
       begin
           sram_address_o   <= reg_address;
           sram_be_o        <= ~reg_wr[1:0];
           sram_data_o      <= reg_data_o[15:0];
           sram_we_o        <= 1'b0;
           
           if (timing_ctrl_i[3:0] != 4'b0000)
           begin
                reg_wait    <= timing_ctrl_i[3:0];
                reg_state   <= MEM_WRITE_WAIT2;
           end
           else
                reg_state   <= MEM_WRITE_DATA2;
       end
       MEM_WRITE_DATA2 : 
       begin 
           sram_we_o    <= 1'b1;
           
           reg_state    <= MEM_IDLE;
           ack_o        <= 1'b1;
       end
       MEM_READ_DATA1 : 
       begin 
           sram_oe_o    <= 1'b0;
           
           reg_data_i    <= {sram_data_i[15:0],16'h0000};
           
           v_reg_address = (reg_address + 1);
           
           sram_address_o <= v_reg_address[(EXT_ADDR_WIDTH - 1):0];
           reg_address    <= v_reg_address;
           
           if (timing_ctrl_i[7:4] != 4'b0000)
           begin
                reg_wait    <= timing_ctrl_i[7:4];
                reg_state   <= MEM_READ_WAIT2;
           end
           else
                reg_state   <= MEM_READ_DATA2;
       end
       MEM_READ_DATA2 : 
       begin
           reg_data_i    <= {reg_data_i[31:16],sram_data_i[15:0]};
           
           sram_oe_o    <= 1'b1;
           
           ack_o        <= 1'b1;
           reg_state    <= MEM_IDLE;
       end
       MEM_READ_WAIT1 : 
       begin
            reg_wait    <= reg_wait - 1;
            
            if (reg_wait == 4'b0001)
            begin
                reg_state   <= MEM_READ_DATA1;
            end
       end       
       MEM_READ_WAIT2 : 
       begin
            reg_wait    <= reg_wait - 1;
            
            if (reg_wait == 4'b0001)
            begin
                reg_state   <= MEM_READ_DATA2;
            end
       end      
       
       MEM_WRITE_WAIT1 : 
       begin
            reg_wait    <= reg_wait - 1;
            
            if (reg_wait == 4'b0001)
            begin
                reg_state   <= MEM_WRITE_DATA1;
            end
       end       
       MEM_WRITE_WAIT2 : 
       begin
            reg_wait    <= reg_wait - 1;
            
            if (reg_wait == 4'b0001)
            begin
                reg_state   <= MEM_WRITE_DATA2;
            end
       end
       MEM_WRITE_HOLD : 
       begin
            reg_wait    <= reg_wait - 1;
            
            if (reg_wait == 4'b0001)
            begin
                reg_state   <= MEM_WRITE_SETUP2;
            end
       end         
       
       default : 
            reg_state   <= MEM_IDLE;
       endcase
   end
end
   
assign data_o        = reg_data_i;
assign busy_o        = (reg_state != MEM_IDLE) ? 1'b1 : 1'b0;
assign sram_cs_o     = 1'b0;

endmodule
