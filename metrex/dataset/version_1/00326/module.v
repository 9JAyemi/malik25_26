
module bmu ( cx0, cx1, bm0, bm1, bm2, bm3, bm4, bm5, bm6, bm7 );
  input cx0, cx1;
  output [1:0] bm0, bm1, bm2, bm3, bm4, bm5, bm6, bm7;

  assign bm0 = cx0 ? 2'b00 : 2'b11;
  assign bm1 = cx0 ? 2'b01 : 2'b10;
  assign bm2 = cx1 ? 2'b00 : 2'b11;
  assign bm3 = cx1 ? 2'b01 : 2'b10;
  assign bm4 = cx1 ? 2'b00 : 2'b11;
  assign bm5 = cx1 ? 2'b01 : 2'b10;
  assign bm6 = cx1 ? 2'b00 : 2'b11;
  assign bm7 = cx1 ? 2'b10 : 2'b01;
endmodule
module add_compare_select_3 ( npm, d, pm1, bm1, pm2, bm2 );
  input [3:0] npm;
  output d;
  input [3:0] pm1, pm2;
  input [1:0] bm1, bm2;

  assign d = ( npm[3] == bm1[1] & npm[2:0] == bm1[0] ) ? pm1[3:0] : pm2[3:0];
endmodule
module add_compare_select_2 ( npm, d, pm1, bm1, pm2, bm2 );
  input [3:0] npm;
  output d;
  input [3:0] pm1, pm2;
  input [1:0] bm1, bm2;

  assign d = ( npm[3:1] == {bm1[1], bm1[0]} ) ? pm1[3:0] : pm2[3:0];
endmodule
module add_compare_select_1 ( npm, d, pm1, bm1, pm2, bm2 );
  input [3:0] npm;
  output d;
  input [3:0] pm1, pm2;
  input [1:0] bm1, bm2;

  assign d = ( npm[3] == bm1[1] ) ? pm1[3:0] : pm2[3:0];
endmodule
module add_compare_select_0 ( npm, d, pm1, bm1, pm2, bm2 );
  input [3:0] npm;
  output d;
  input [3:0] pm1, pm2;
  input [1:0] bm1, bm2;

  assign d = pm1[3:0];
endmodule
module pmsm ( npm0, npm1, npm2, npm3, pm0, pm1, pm2, pm3, clk, reset );
  input [3:0] npm0, npm1, npm2, npm3;
  output [3:0] pm0, pm1, pm2, pm3;
  input clk, reset;

  reg [3:0] pm0_reg, pm1_reg, pm2_reg, pm3_reg;

  always @(posedge clk or posedge reset) begin
    if (reset) begin
      pm0_reg <= 4'b0;
      pm1_reg <= 4'b0;
      pm2_reg <= 4'b0;
      pm3_reg <= 4'b0;
    end else begin
      pm0_reg <= npm0;
      pm1_reg <= npm1;
      pm2_reg <= npm2;
      pm3_reg <= npm3;
    end
  end

  assign pm0 = pm0_reg;
  assign pm1 = pm1_reg;
  assign pm2 = pm2_reg;
  assign pm3 = pm3_reg;
endmodule
module spd ( d0, d1, d2, d3, pm0, pm1, pm2, pm3, out, clk, reset );
  input d0, d1, d2, d3;
  input [3:0] pm0, pm1, pm2, pm3;
  output out;
  input clk, reset;

  reg [3:0] pm_reg;
  reg out_reg;

  always @(posedge clk or posedge reset) begin
    if (reset) begin
      pm_reg <= 4'b0;
      out_reg <= 0;
    end else begin
      pm_reg <= {pm_reg[2:0], out_reg};
      out_reg <= (pm_reg == pm0);
    end
  end

  assign out = out_reg;
endmodule
module viterbi_decoder ( d, cx, clk, reset );
  input [1:0] cx;
  input clk, reset;
  output d;

  wire d0, d1, d2, d3;
  wire [1:0] brch_met0, brch_met1, brch_met2, brch_met3;
  wire [3:0] p_m0, p_m1, p_m2, p_m3;

  bmu brch_met ( .cx0(cx[0]), .cx1(cx[1]), .bm0(brch_met0), .bm1(brch_met1),
        .bm2(brch_met2), .bm3(brch_met3) );

  add_compare_select_3 acs0 ( .npm(p_m0), .d(d0), .pm1(p_m0), .bm1(brch_met0),
        .pm2(p_m1), .bm2(brch_met2) );

  add_compare_select_2 acs1 ( .npm(p_m1), .d(d1), .pm1(p_m2), .bm1(brch_met0),
        .pm2(p_m3), .bm2(brch_met1) );

  add_compare_select_1 acs2 ( .npm(p_m2), .d(d2), .pm1(p_m0), .bm1(brch_met3),
        .pm2(p_m1), .bm2(brch_met1) );

  add_compare_select_0 acs3 ( .npm(p_m3), .d(d3), .pm1(p_m2), .bm1(brch_met3),
        .pm2(p_m3), .bm2(brch_met2) );

  pmsm path_metric_sm ( .npm0(p_m0), .npm1(p_m1), .npm2(p_m2), .npm3(p_m3),
        .pm0(p_m0), .pm1(p_m1), .pm2(p_m2), .pm3(p_m3), .clk(clk), .reset(
        reset) );

  spd survivor_path_dec ( .d0(d0), .d1(d1), .d2(d2), .d3(d3), .pm0(p_m0),
        .pm1(p_m1), .pm2(p_m2), .pm3(p_m3), .out(d), .clk(clk), .reset(reset)
         );

endmodule