// SVA for big_lcd
module big_lcd_sva(
  input  logic        clk,
  input  logic        reset,
  input  logic [15:0] lcd_readdata,
  input  logic        lcd_read,
  input  logic [7:0]  R,G,B,
  input  logic        HSYNC, VSYNC, LCD_CLK,
  input  logic [10:0] counter_hs, counter_vs,
  input  logic        data_en
);

  default clocking @(posedge clk); endclocking

  // No Xs on key outputs once running
  a_no_x: assert property (reset && $past(reset) |-> !$isunknown({HSYNC,VSYNC,R,G,B,LCD_CLK,lcd_read}));

  // Reset behavior (active-low)
  a_rst_zero_now:  assert property (!reset |-> counter_hs==11'd0 && counter_vs==11'd0);
  a_rst_hold_zero: assert property (!reset |=> $stable(counter_hs) && $stable(counter_vs));

  // Counter ranges
  a_hs_range: assert property (counter_hs <= 11'd1055);
  a_vs_range: assert property (counter_vs <= 11'd524);

  // Counters increment and wrap
  a_inc:  assert property (reset && $past(reset) && $past(counter_hs)!=11'd1055
                           |-> counter_hs==$past(counter_hs)+11'd1 && counter_vs==$past(counter_vs));
  a_wrap: assert property (reset && $past(reset) && $past(counter_hs)==11'd1055
                           |-> counter_hs==11'd0 &&
                               counter_vs==(($past(counter_vs)==11'd524)? 11'd0 : $past(counter_vs)+11'd1));

  // HSYNC/VSYNC mapping
  a_hsync_map: assert property (HSYNC == (counter_hs >= 11'd10));
  a_vsync_map: assert property (VSYNC == (counter_vs >= 11'd10));

  // Read/data enable windows
  a_lcd_read_map: assert property (lcd_read == (counter_hs>=11'd42 && counter_hs<=11'd681 &&
                                                counter_vs>=11'd23 && counter_vs<11'd503));
  a_data_en_map:  assert property (data_en  == (counter_hs>=11'd46 && counter_hs<=11'd686 &&
                                                counter_vs>=11'd23 && counter_vs<11'd503));

  // RGB mapping
  a_data_colors:  assert property (data_en |-> (R=={lcd_readdata[15:11], lcd_readdata[15:13]} &&
                                                G=={lcd_readdata[10:5],  lcd_readdata[10:9]}  &&
                                                B=={lcd_readdata[4:0],   lcd_readdata[4:2]}));
  a_blank_colors: assert property (!data_en |-> (R==8'hff && G==8'h00 && B==8'h0f));

  // LCD clock gating (both edges)
  a_lcd_clk_pos_run: assert property (@(posedge clk) (reset  |-> LCD_CLK==1'b1));
  a_lcd_clk_pos_rst: assert property (@(posedge clk) (!reset |-> LCD_CLK==1'b0));
  a_lcd_clk_neg_run: assert property (@(negedge clk) (reset  |-> LCD_CLK==1'b0));
  a_lcd_clk_neg_rst: assert property (@(negedge clk) (!reset |-> LCD_CLK==1'b0));

  // Coverage
  c_top_left:        cover property (reset && counter_hs==11'd0 && counter_vs==11'd0);
  c_hsync_pulse:     cover property ($fell(HSYNC) ##[1:$] $rose(HSYNC));
  c_vsync_pulse:     cover property ($fell(VSYNC) ##[1:$] $rose(VSYNC));
  c_lcd_read_start:  cover property (reset && counter_vs>=11'd23 && counter_vs<11'd503 &&
                                     counter_hs==11'd42 && lcd_read);
  c_lcd_read_end:    cover property (reset && counter_vs>=11'd23 && counter_vs<11'd503 &&
                                     counter_hs==11'd681 && lcd_read);
  c_de_start:        cover property (reset && counter_vs>=11'd23 && counter_vs<11'd503 &&
                                     counter_hs==11'd46 && data_en);
  c_de_end_fall:     cover property (reset && counter_vs>=11'd23 && counter_vs<11'd503 &&
                                     counter_hs==11'd686 && data_en ##1 !data_en);
  c_vactive_start:   cover property (reset && counter_vs==11'd23  && counter_hs==11'd0);
  c_vactive_end:     cover property (reset && counter_vs==11'd502 && counter_hs==11'd0);

endmodule

bind big_lcd big_lcd_sva big_lcd_sva_i(.*);