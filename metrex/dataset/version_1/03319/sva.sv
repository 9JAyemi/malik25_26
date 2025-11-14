// SVA for hi_sniffer. Focused, high-quality checks with concise coverage.

module hi_sniffer_sva (
  input  logic        ck_1356meg,
  input  logic        ssp_clk,
  input  logic        adc_clk,
  input  logic [7:0]  adc_d,
  input  logic [7:0]  adc_d_out,
  input  logic [2:0]  ssp_cnt,
  input  logic        ssp_frame,
  input  logic        ssp_din,
  input  logic        pwr_lo, pwr_hi, pwr_oe1, pwr_oe2, pwr_oe3, pwr_oe4
);

  // Power pins hard-tied low
  assert property (@(posedge ck_1356meg) !pwr_lo && !pwr_hi && !pwr_oe1 && !pwr_oe2 && !pwr_oe3 && !pwr_oe4);

  // Clock wiring
  assert property (@(posedge ck_1356meg)  adc_clk && !ssp_clk);
  assert property (@(negedge ck_1356meg) !adc_clk &&  ssp_clk);

  // Default clock for sequential behavior
  default clocking cb @ (posedge ssp_clk); endclocking

  // ssp_cnt next-state (mod-8 up-counter)
  assert property ( ssp_cnt == (($past(ssp_cnt,1,3'd0) == 3'd7) ? 3'd0 : $past(ssp_cnt,1,3'd0) + 3'd1) );

  // ssp_frame next-state equals (previous ssp_cnt == 0)
  assert property ( ssp_frame == ($past(ssp_cnt,1,3'd0) == 3'd0) );

  // Shift/load behavior of adc_d_out (load on prev cnt==0, else shift right with zero fill)
  assert property ( adc_d_out ==
                    ( ($past(ssp_cnt,1,3'd0) == 3'd0)
                      ? $past(adc_d,1,8'h00)
                      : {1'b0, $past(adc_d_out,1,8'h00)[7:1]} ) );

  // ssp_din is always LSB of adc_d_out
  assert property ( ssp_din == adc_d_out[0] );

  // Basic range sanity (defensive)
  assert property ( ssp_cnt inside {[3'd0:3'd7]} );

  // Coverage: full 8-cycle frame of ssp_cnt
  cover property ( ssp_cnt==3'd0 ##1 ssp_cnt==3'd1 ##1 ssp_cnt==3'd2 ##1 ssp_cnt==3'd3
                   ##1 ssp_cnt==3'd4 ##1 ssp_cnt==3'd5 ##1 ssp_cnt==3'd6 ##1 ssp_cnt==3'd7 ##1 ssp_cnt==3'd0 );

  // Coverage: frame pulse observed on load cycle
  cover property ( ($past(ssp_cnt,1,3'd0)==3'd0) && ssp_frame );

  // Coverage: serialized output matches captured adc_d bits (LSB first over 8 cycles)
  cover property (
    ($past(ssp_cnt,1,3'd0)==3'd0)
    ##1 (ssp_din == $past(adc_d,1,8'h00)[0])
    ##1 (ssp_din == $past(adc_d,2,8'h00)[1])
    ##1 (ssp_din == $past(adc_d,3,8'h00)[2])
    ##1 (ssp_din == $past(adc_d,4,8'h00)[3])
    ##1 (ssp_din == $past(adc_d,5,8'h00)[4])
    ##1 (ssp_din == $past(adc_d,6,8'h00)[5])
    ##1 (ssp_din == $past(adc_d,7,8'h00)[6])
    ##1 (ssp_din == $past(adc_d,8,8'h00)[7])
  );

endmodule

bind hi_sniffer hi_sniffer_sva sva (
  .ck_1356meg(ck_1356meg),
  .ssp_clk(ssp_clk),
  .adc_clk(adc_clk),
  .adc_d(adc_d),
  .adc_d_out(adc_d_out),
  .ssp_cnt(ssp_cnt),
  .ssp_frame(ssp_frame),
  .ssp_din(ssp_din),
  .pwr_lo(pwr_lo), .pwr_hi(pwr_hi),
  .pwr_oe1(pwr_oe1), .pwr_oe2(pwr_oe2), .pwr_oe3(pwr_oe3), .pwr_oe4(pwr_oe4)
);