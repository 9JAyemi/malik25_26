

module dlp_reg
  (
   input  	hb_clk,         
   input 	hb_rstn,        
   input        dlp_rstn_hb,    input [8:2] 	hb_adr,         
   input 	hb_wstrb,       
   input [3:0] 	hb_ben,         
   input 	hb_csn,       	
   input [31:0] hb_din,         
   input [8:2] 	de_adr,         
   input 	de_wstrb,       
   input [3:0] 	de_ben,         
   input 	de_csn,       	
   input [31:0] de_din,         
   input 	actv_stp,       
   input 	next_dle,       
   input 	cmd_ack,        
   input        reset_wait,     input [3:0]  dlp_offset,     output reg [27:0] hb_addr,    
   output reg [27:0] hb_end,     
   output 	 hb_fmt,         
   output 	 hb_wc,          
   output 	 hb_sen,         
   output 	 hb_stp,         
   output reg	 dlp_actv_2,     
   output 	 dl_idle,        
   output reg	 hold_start,     
   output reg 	 cmd_rdy_ld,     
   output 	 wcf,            
   output reg    [4:0]  dlp_wcnt 
   );
  
  `define DLP_BURST_SIZE 28'h8
  `define DLP_BURST_SIZE_M1 5'h7

  reg signed [28:0] 	remainder;
  reg 		dl_cmd_strb;    
  reg 		start_strobe;   
  reg [27:0] 	hb_addr1;     
  reg [27:0] 	hb_end1;      
  reg 		wc1;          
  reg [3:0] 	hb_cntrl_w1;  
  reg 		wc2;          
  reg [3:0] 	hb_cntrl_w2;  
  reg [1:0] 	adr_cntrl2;   
  reg [1:0] 	adr_cntrl1;   
  
  wire 		next_stp;       
  wire 		toggle_out;     
  wire 		dlp_hb_w;       
  wire 		dlp_de_w;       
  wire 		start_strobe_comb;
  
  parameter 	DLCNT_DLADR	= 6'b0_1111_1;	

  always @(posedge hb_clk or negedge hb_rstn) begin
    if (!hb_rstn)            cmd_rdy_ld <= 1'b0;
    else if (dlp_rstn_hb)    cmd_rdy_ld <= 1'b0;
    else if (dl_cmd_strb || start_strobe && dl_idle)  cmd_rdy_ld <= 1'b1;
    else if (cmd_ack)        cmd_rdy_ld <= 1'b0;
  end

  
  
  
  
  assign dlp_hb_w = (hb_adr[8:3]==DLCNT_DLADR) && hb_wstrb && !hb_csn;
  assign dlp_de_w = (de_adr[8:3]==DLCNT_DLADR) && de_wstrb && !de_csn;

  assign start_strobe_comb = 	((dlp_hb_w & ~hb_ben[3] & ~hb_adr[2]) |
				 (dlp_de_w & ~de_adr[2]));

  wire 	 	 stop_list;
  assign 	 stop_list = ~hb_cntrl_w2[3] && hb_cntrl_w1[3];

  always @(posedge hb_clk) begin
    if (!hb_rstn) begin
      dl_cmd_strb  <= 1'b0;
      hb_addr1     <= 28'b0;
      hb_end1      <= 28'b0;
      adr_cntrl1   <= 2'b0;
      wc1          <= 1'b0;
      hb_cntrl_w1  <= 4'b0;
      hb_addr      <= 28'b0;
      hb_end       <= 28'b0;
      hb_cntrl_w2  <= 4'b1000;
      start_strobe <= 1'b0;
      adr_cntrl2   <= 2'b0;
      wc2          <= 1'b0;
      hold_start   <= 1'b0;
       remainder   <= 0;
    end else if (dlp_rstn_hb) begin
      dl_cmd_strb  <= 1'b0;
      start_strobe <= 1'b0;
      hb_cntrl_w2  <= 4'b1000;
      hold_start   <= 1'b0;
       remainder   <= 0;
    end else begin
       remainder <= (hb_end - hb_addr);
      if (start_strobe_comb) start_strobe <= 1'b1;
      
      
      
      if (dlp_hb_w && ~hb_adr[2]) begin
	hold_start <= 1'b1;
	if(!hb_ben[0]) hb_addr1[3:0]   <= hb_din[7:4];
	if(!hb_ben[1]) hb_addr1[11:4]  <= hb_din[15:8];
	if(!hb_ben[2]) hb_addr1[19:12] <= hb_din[23:16];
	if(!hb_ben[3]) begin
	  hb_addr1[27:20] <= {dlp_offset, hb_din[27:24]};
	end
	if(!hb_ben[3]) adr_cntrl1      <= hb_din[30:29];
	if(!hb_ben[3]) wc1             <= hb_din[31];
      end else if (dlp_de_w && ~de_adr[2]) begin
	hold_start <= 1'b1;
	if(!de_ben[0]) hb_addr1[3:0]   <= de_din[7:4];
	if(!de_ben[1]) hb_addr1[11:4]  <= de_din[15:8];
	if(!de_ben[2]) hb_addr1[19:12] <= de_din[23:16];
	if(!de_ben[3]) begin
	  hb_addr1[27:20] <= {dlp_offset, de_din[27:24]};
	end
	if(!de_ben[3]) adr_cntrl1      <= de_din[30:29]; if(!de_ben[3]) wc1             <= de_din[31];
      end
      
      
      
      
      
      
      if (dlp_hb_w && hb_adr[2]) begin
	dl_cmd_strb <= ~hb_ben[3];
	if(!hb_ben[0]) hb_end1[3:0]     <= hb_din[7:4];
	if(!hb_ben[1]) hb_end1[11:4]    <= hb_din[15:8];
	if(!hb_ben[2]) hb_end1[19:12]   <= hb_din[23:16];
	if(!hb_ben[3]) begin
	  hb_end1[27:20]   <= {dlp_offset, hb_din[27:24]};
	end
	if(!hb_ben[3]) hb_cntrl_w1[3:0] <= hb_din[31:28];
      end else if (dlp_de_w && de_adr[2]) begin 
	dl_cmd_strb <= ~de_ben[3];
	if(!de_ben[0]) hb_end1[3:0]     <= de_din[7:4];
	if(!de_ben[1]) hb_end1[11:4]    <= de_din[15:8];
	if(!de_ben[2]) hb_end1[19:12]   <= de_din[23:16];
	if(!de_ben[3]) begin
	  hb_end1[27:20]   <= {dlp_offset, de_din[27:24]};
	end
	if(!de_ben[3]) hb_cntrl_w1[3:0] <= de_din[31:28];
      end

      
      
      
      if (reset_wait) adr_cntrl2[0] <= 1'b0;

      if (dl_cmd_strb && ~hold_start && stop_list && ~dl_idle) begin
	hb_addr      <= hb_end1-28'h1;
	start_strobe <= 1'b0;
	dl_cmd_strb  <= 1'b0;
	end else if (start_strobe && dl_idle) begin
	hold_start   <= 1'b0;
	start_strobe <= 1'b0;
	hb_addr      <= hb_addr1;
	adr_cntrl2   <= adr_cntrl1;
	wc2          <= wc1;
      end else if (next_dle && ~dl_idle) 
	hb_addr      <= hb_addr + 28'h1;


      if (dl_cmd_strb && ~hold_start)
      begin
	hb_end      <= hb_end1;
	hb_cntrl_w2 <= hb_cntrl_w1;
	dl_cmd_strb <= 1'b0;
      end 
      else if (dl_idle && ~start_strobe) 
	hb_cntrl_w2[3] <= 1'b1;

    end end 
   always @*
    if(remainder > `DLP_BURST_SIZE) dlp_wcnt = `DLP_BURST_SIZE_M1;
    else dlp_wcnt = remainder -1'b1;
      
  
  
  
  assign hb_fmt  = hb_cntrl_w2[1];
  assign hb_sen  = hb_cntrl_w2[2];
  assign hb_stp  = hb_cntrl_w2[3];
  assign hb_wc   = wc2;
  assign wcf     = adr_cntrl2[0];
  
  
  
  

  reg dl_idle_hold;
  
  assign dl_idle = (hb_addr == hb_end) | dl_idle_hold; always @(posedge hb_clk, negedge hb_rstn) begin
    if (!hb_rstn)            		 dl_idle_hold <= 1'b0;
    else if (dl_cmd_strb && ~hold_start) dl_idle_hold <= 1'b0;
    else if (hb_stp || dl_idle) 	 dl_idle_hold <= 1'b1;
  end

  assign next_stp = hb_cntrl_w2[3];
  assign toggle_out = dl_idle & ~next_stp;
  
  
  
  
  always @(posedge hb_clk or negedge hb_rstn) begin
    if(!hb_rstn)                     			     dlp_actv_2 <= 1'b0;
    else if(dlp_rstn_hb)             			     dlp_actv_2 <= 1'b0;
    else if ((dl_cmd_strb && ~hb_cntrl_w1[3]) || toggle_out) dlp_actv_2 <= 1'b1;
    else if ((~actv_stp && dl_idle && next_stp) ||
	     (dl_cmd_strb && hb_cntrl_w1[3])) 		     dlp_actv_2 <= 1'b0;
  end

endmodule
