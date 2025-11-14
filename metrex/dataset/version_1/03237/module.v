


module speed_neg_control (

  input  wire        clk,        input  wire        reset,      input  wire        link_reset,
  output reg         mgt_reset,  input  wire        linkup,     output reg   [6:0] daddr,      output reg         den,        output reg  [15:0] di,         input  wire [15:0] do,         input  wire        drdy,       output reg         dwe,        input  wire        gtp_lock,   output wire  [4:0] state_out,
  output reg         gen_value  
);
	

	parameter	[4:0] 	IDLE		= 5'h00;
	parameter	[4:0] 	READ_GEN2  	= 5'h01;
	parameter	[4:0] 	WRITE_GEN2  	= 5'h02;
	parameter	[4:0] 	COMPLETE_GEN2  	= 5'h03;
	parameter	[4:0] 	PAUSE1_GEN2  	= 5'h04;
	parameter	[4:0] 	READ1_GEN2  	= 5'h05;
	parameter	[4:0] 	WRITE1_GEN2  	= 5'h06;
	parameter	[4:0] 	COMPLETE1_GEN2  = 5'h07;
	parameter	[4:0] 	RESET 	 	= 5'h08;
	parameter	[4:0] 	WAIT_GEN2   	= 5'h09;
	parameter	[4:0] 	READ_GEN1  	= 5'h0A;
	parameter	[4:0] 	WRITE_GEN1  	= 5'h0B;
	parameter	[4:0] 	COMPLETE_GEN1  	= 5'h0C;
	parameter	[4:0] 	PAUSE_GEN1 	= 5'h0D;
	parameter	[4:0] 	READ1_GEN1  	= 5'h0E;
	parameter	[4:0] 	WRITE1_GEN1  	= 5'h0F;
	parameter	[4:0] 	COMPLETE1_GEN1  = 5'h10;
	parameter	[4:0] 	RESET_GEN1  	= 5'h11;
	parameter	[4:0] 	WAIT_GEN1   	= 5'h12;
	parameter	[4:0] 	LINKUP 		= 5'h13;


	reg  [4:0] state;
	reg [31:0] linkup_cnt;
	reg [15:0] drp_reg;
	reg [15:0] reset_cnt;
	reg  [3:0] pause_cnt;

assign state_out = state;

always @ (posedge clk or posedge reset)
begin
  if(reset)
  begin
    state <= IDLE;
    daddr <= 7'b0;
    di    <= 8'b0;
    den   <= 1'b0;
    dwe   <= 1'b0;
    drp_reg <= 16'b0;
    linkup_cnt <= 32'h0;
    gen_value <= 1'b1;
    reset_cnt <= 16'b0000000000000000;
    mgt_reset <= 1'b0;
    pause_cnt <= 4'b0000;

  end
  else
  begin
  	case(state)
      	IDLE:  begin
              	if(gtp_lock)
			begin
			daddr <= 7'h46;
                	den   <= 1'b1;
                	gen_value    <= 1'b1; state      <= READ_GEN2;        
			end
			else
			begin
			    state <= IDLE;
			end
             end
      READ_GEN2: begin
               if(drdy)
               begin
                 drp_reg <= do;
                 den   <= 1'b0;
                 state <= WRITE_GEN2;
               end
               else
               begin
                 state <= READ_GEN2;
               end
             end
      WRITE_GEN2: begin
               di  <= drp_reg ;  di[2] <= 1'b0;
               den <= 1'b1;
               dwe <= 1'b1;
               state <= COMPLETE_GEN2;
             end
      COMPLETE_GEN2: begin
               if(drdy)
               begin
                 dwe   <= 1'b0;
                 den   <= 1'b0;
                 state <= PAUSE1_GEN2;
               end
               else
               begin
                 state <= COMPLETE_GEN2;
               end
             end
      PAUSE1_GEN2: begin
               if(pause_cnt == 4'b1111)
               begin
                 dwe   <= 1'b0;
                 den   <= 1'b1;
                 daddr <= 7'h45;
                 pause_cnt <= 4'b0000;
                 state <= READ1_GEN2;
               end
               else
               begin
                 pause_cnt <= pause_cnt + 1'b1;
                 state <= PAUSE1_GEN2;
               end
             end           
      READ1_GEN2: begin
               if(drdy)
               begin
                 drp_reg <= do;
                 den   <= 1'b0;
                 state <= WRITE1_GEN2;
               end
               else
               begin
                 state <= READ1_GEN2;
               end
             end
      WRITE1_GEN2: begin
               di  <= drp_reg;  
               di[15] <= 1'b0;
               den <= 1'b1;
               dwe <= 1'b1;
               state <= COMPLETE1_GEN2;
             end
      COMPLETE1_GEN2: begin
               if(drdy)
               begin
                 dwe   <= 1'b0;
                 den   <= 1'b0;
                 state <= RESET;
               
               end
               else
               begin
                 state <= COMPLETE1_GEN2;
               end
             end
     
      RESET: begin
               if(reset_cnt == 16'b00001111)
               begin
                 reset_cnt <= reset_cnt + 1'b1;
                 state <= RESET;
                 mgt_reset <= 1'b1;
               end
               else if(reset_cnt == 16'b0000000000011111)
               begin
                 reset_cnt <= 16'b00000000;
                 mgt_reset <= 1'b0;
                 state <= WAIT_GEN2;
               end
               else
               begin
                 reset_cnt <= reset_cnt + 1'b1;
                 state <= RESET;
               end
             end
      WAIT_GEN2:  begin if(linkup)
               begin
                 linkup_cnt <= 32'h0;
                 state <= LINKUP;
               end
               else
               begin
		if(gtp_lock)
		begin
		`ifdef SIM 
		   if(linkup_cnt == 32'h000007FF) `else					  
                   if(linkup_cnt == 32'h00080EB4) `endif 
                   begin
                     linkup_cnt <= 32'h0;
                     daddr <= 7'h46;
                     den   <= 1'b1;
                     gen_value <= 1'b0; state      <= READ_GEN1;
			  end
                   else
                   begin
                     linkup_cnt <= linkup_cnt + 1'b1;
                     state <= WAIT_GEN2;
                   end
					  end
					  else
					  begin
					    state <= WAIT_GEN2;
					  end
               end

             end
      READ_GEN1: begin
               if(drdy)
               begin
                 drp_reg <= do;
                 den   <= 1'b0;
                 state <= WRITE_GEN1;
               end
               else
               begin
                 state <= READ_GEN1;
               end
             end
      WRITE_GEN1: begin
               di  <= drp_reg;  di[2] <=  1'b1;
               den <= 1'b1;
               dwe <= 1'b1;
               state <= COMPLETE_GEN1;
             end
      COMPLETE_GEN1: begin
               if(drdy)
               begin
                 dwe   <= 1'b0;
                 den   <= 1'b0;
                 state <= PAUSE_GEN1;
               end
               else
               begin
                 state <= COMPLETE_GEN1;
               end
             end
     PAUSE_GEN1: begin
               if(pause_cnt == 4'b1111)
               begin
                 dwe   <= 1'b0;
                 den   <= 1'b1;
                 daddr <= 7'h45;
                 pause_cnt <= 4'b0000;
                 state <= READ1_GEN1;
               end
               else
               begin
                 pause_cnt <= pause_cnt + 1'b1;
                 state <= PAUSE_GEN1;
               end
             end 
      READ1_GEN1: begin
               if(drdy)
               begin
                 drp_reg <= do;
                 den   <= 1'b0;
                 state <= WRITE1_GEN1;
               end
               else
               begin
                 state <= READ1_GEN1;
               end
             end
      WRITE1_GEN1: begin
               di  <= drp_reg;  di[15] <= 1'b1;
               den <= 1'b1;
               dwe <= 1'b1;
               state <= COMPLETE1_GEN1;
             end
      COMPLETE1_GEN1: begin
               if(drdy)
               begin
                 dwe   <= 1'b0;
                 den   <= 1'b0;
                 state <= RESET_GEN1;
               
               end
               else
               begin
                 state <= COMPLETE1_GEN1;
               end
             end
     
      RESET_GEN1: begin
               if(reset_cnt == 16'b00001111)
               begin
                 reset_cnt <= reset_cnt + 1'b1;
                 state <= RESET_GEN1;
                 mgt_reset <= 1'b1;
               end
               else if(reset_cnt == 16'h001F)
               begin
                 reset_cnt <= 16'b00000000;
                 mgt_reset <= 1'b0;
                 state <= WAIT_GEN1;
               end
               else
               begin
                 reset_cnt <= reset_cnt + 1'b1;
                 state <= RESET_GEN1;
               end
             end
      WAIT_GEN1:  begin
               if(linkup)
               begin
                 linkup_cnt <= 32'h0;
                 state <= LINKUP;
               end
               else
               begin
		if(gtp_lock)
		begin
		`ifdef SIM 
		   if(linkup_cnt == 32'h000007FF) `else					  
                   if(linkup_cnt == 32'h00080EB4) `endif 
                   begin
                     linkup_cnt <= 32'h0;
                     daddr <= 7'h46;
                     den   <= 1'b1;
                     state <= READ_GEN2; end
                   else
                   begin
                     linkup_cnt <= linkup_cnt + 1'b1;
                     state <= WAIT_GEN1;
                   end
		 end
		 else
		  begin
		    state <= WAIT_GEN1;
		  end
               end

             end                         
     LINKUP: begin
     		if (linkup)
               		state <= LINKUP;
               	else
                   begin
                     linkup_cnt <= 32'h0;
                     daddr <= 7'h46;
                     den   <= 1'b1;
                     state <= READ_GEN2; end               		
             end 

     default: begin
                state <= IDLE;
                daddr <= 7'b0;
                di    <= 8'b0;
                den   <= 1'b0;
                dwe   <= 1'b0;
                drp_reg <= 16'b0;
                linkup_cnt <= 32'h0;
                gen_value <= 1'b1;
                reset_cnt <= 8'b00000000;
                mgt_reset <= 1'b0;
                pause_cnt <= 4'b0000;
              end 
    endcase
  end

end

endmodule
