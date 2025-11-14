

module tg_prbs_gen #
  (
    parameter PRBS_WIDTH = 64,          parameter START_ADDR  = 32'h00000000,
    parameter DMODE = "READ",
    parameter PRBS_OFFSET = 0, 
    parameter [PRBS_WIDTH-1:0] TAPS= 32'h80200003 )
  (
   input           clk_i,
   input           clk_en,
   input           rst,
input [PRBS_WIDTH-1:0]    prbs_seed_i,
   output                    initialize_done,
   output  [PRBS_WIDTH-1:0]  prbs_o,     output reg [3:0] prbs_shift_value,
   output [31:0] ReSeedcounter_o
  );
  
  
wire  prbs_seed_ld;
reg [PRBS_WIDTH - 1:0] Next_LFSR_Reg;
reg [PRBS_WIDTH - 1:0] LFSR_Reg;
reg [PRBS_WIDTH-1:0] counterA;
reg Bits0_9_zero, Feedback;
integer i;
reg [PRBS_WIDTH - 1:0] ReSeedcounter;
reg [10:0] freerun_counters;
reg init_setup;
wire prbs_clk_en1;
wire prbs_clk_en2;
always @ (posedge clk_i)
begin
   if (rst)
     freerun_counters <= 'b0;
   else if (freerun_counters <= 128 || init_setup)
     freerun_counters <= freerun_counters + 1'b1;
end


always @ (posedge clk_i)
begin
   if (rst)
     counterA <= 'b0;
else if (prbs_clk_en1)

     counterA <= counterA + 1'b1;
end




assign initialize_done = ~init_setup;
always @ (posedge clk_i)
begin
   if (rst)
     init_setup <= 'b0;
   else if ( freerun_counters <= PRBS_OFFSET + 255 )
     init_setup <= 1'b1;
   else
     init_setup <= 1'b0;
    
end



assign ReSeedcounter_o = {{(32-PRBS_WIDTH){1'b0}},ReSeedcounter};
always @ (posedge clk_i)
begin
   if (rst)
     ReSeedcounter <= 'b0;
   else if (prbs_clk_en1)
     if (ReSeedcounter == {PRBS_WIDTH {1'b1}})
         ReSeedcounter <= 'b0;
     else
         ReSeedcounter <= ReSeedcounter + 1'b1;
end


assign prbs_clk_en1 = clk_en | init_setup ;
assign prbs_clk_en2 = clk_en | init_setup ;

always @ (posedge clk_i)
begin
   if (rst  ) begin
        LFSR_Reg[3:0] <=  prbs_seed_i[3:0] | 4'h5;
        LFSR_Reg[PRBS_WIDTH-1:4] <= prbs_seed_i[PRBS_WIDTH-1:4];
    end
   else if (prbs_clk_en2) begin
     LFSR_Reg <= Next_LFSR_Reg;
        prbs_shift_value <= {prbs_shift_value[2:0],LFSR_Reg[PRBS_WIDTH-1]};
        end
end

   

always @ (LFSR_Reg)
begin :LFSR_Feedback
   Bits0_9_zero = ~| LFSR_Reg[PRBS_WIDTH-2:0];
   Feedback = LFSR_Reg[PRBS_WIDTH-1]^Bits0_9_zero; 
for (i = PRBS_WIDTH - 1; i >= 1 ; i = i-1)

      if (TAPS[i - 1] == 1)
         Next_LFSR_Reg[i]= LFSR_Reg[i-1] ^ Feedback  ;
      else
         Next_LFSR_Reg[i] = LFSR_Reg[i-1];
         
   Next_LFSR_Reg[0] = Feedback  ;end
assign prbs_o = LFSR_Reg;



endmodule
   
         
