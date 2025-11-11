
module tx_reset_sm
(
input        refclkdiv2,
input        rst_n,
input        tx_pll_lol_qd_s,
                                                                                              
output   reg    tx_pcs_rst_ch_c,      output   reg    rst_qd_c          );
                                                                                              
                                                                                              
parameter count_index = 17;
                                                                                              
                                                                                              
localparam   QUAD_RESET      = 0,
             WAIT_FOR_TIMER1       = 1,
             CHECK_PLOL       = 2,
             WAIT_FOR_TIMER2       = 3,
             NORMAL    = 4;
                                                                                              
localparam STATEWIDTH =3;
reg [STATEWIDTH-1:0]    cs ;               reg [STATEWIDTH-1:0]    ns;               reg tx_pll_lol_qd_s_int;
reg tx_pll_lol_qd_s_int1;
reg    [3:0]   tx_pcs_rst_ch_c_int;      reg       rst_qd_c_int;          always @(posedge refclkdiv2 or negedge rst_n)
   begin
   if (rst_n == 1'b0)
      begin
      cs                     <= QUAD_RESET;
      tx_pll_lol_qd_s_int    <= 1;
      tx_pll_lol_qd_s_int1   <= 1;
      tx_pcs_rst_ch_c        <= 1'b1;
      rst_qd_c               <= 1;
      end
   else
      begin
      cs <= ns;
      tx_pll_lol_qd_s_int1   <= tx_pll_lol_qd_s;
      tx_pll_lol_qd_s_int    <= tx_pll_lol_qd_s_int1;
      tx_pcs_rst_ch_c        <= tx_pcs_rst_ch_c_int[0];
      rst_qd_c               <= rst_qd_c_int;
      end
   end
                                                                                              
reg reset_timer1, reset_timer2;
                                                                                              
                                                                                              
localparam TIMER1WIDTH=3;
reg [TIMER1WIDTH-1:0] counter1;
reg TIMER1;
                                                                                              
always @(posedge refclkdiv2 or posedge reset_timer1)
   begin
   if (reset_timer1)
      begin
      counter1 <= 0;
      TIMER1 <= 0;
      end
   else
      begin
      if (counter1[2] == 1)
         TIMER1 <=1;
      else
         begin
         TIMER1 <=0;
         counter1 <= counter1 + 1 ;
         end
      end
   end
                                                                                              
localparam TIMER2WIDTH=18;
reg [TIMER2WIDTH-1:0] counter2;
reg TIMER2;
                                                                                              
always @(posedge refclkdiv2 or posedge reset_timer2)
   begin
   if (reset_timer2)
      begin
      counter2 <= 0;
      TIMER2 <= 0;
      end
   else
      begin
if (counter2[count_index] == 1)
         TIMER2 <=1;
      else
         begin
         TIMER2 <=0;
         counter2 <= counter2 + 1 ;
         end
      end
   end
                                                                                              
                                                                                              
always @(*)
   begin : NEXT_STATE
   reset_timer1 = 0;
   reset_timer2 = 0;
         case (cs)
                                                                                              
            QUAD_RESET: begin
               tx_pcs_rst_ch_c_int = 4'hF;
               rst_qd_c_int = 1;
               reset_timer1 = 1;
               ns = WAIT_FOR_TIMER1;
               end
                                                                                              
            WAIT_FOR_TIMER1: begin
               tx_pcs_rst_ch_c_int = 4'hF;
               rst_qd_c_int = 1;
               if (TIMER1)
                  ns = CHECK_PLOL;
               else
                  ns = WAIT_FOR_TIMER1;
            end
                                                                                              
            CHECK_PLOL: begin
               tx_pcs_rst_ch_c_int = 4'hF;
               rst_qd_c_int = 0;
               reset_timer2 = 1;
               ns = WAIT_FOR_TIMER2;
            end
                                                                                              
            WAIT_FOR_TIMER2: begin
               tx_pcs_rst_ch_c_int = 4'hF;
               rst_qd_c_int = 0;
               if (TIMER2)
                  if (tx_pll_lol_qd_s_int)
                     ns = QUAD_RESET;
                  else
                     ns = NORMAL;
               else
                     ns = WAIT_FOR_TIMER2;
            end
                                                                                              
            NORMAL: begin
               tx_pcs_rst_ch_c_int = 4'h0;
               rst_qd_c_int = 0;
               if (tx_pll_lol_qd_s_int)
                  ns = QUAD_RESET;
               else
                  ns = NORMAL;
            end
                                                                                              
                                                                                              
                                                                                              
            default: begin
               tx_pcs_rst_ch_c_int = 4'hF;
               rst_qd_c_int = 1;
               ns = QUAD_RESET;
            end
         endcase end endmodule
