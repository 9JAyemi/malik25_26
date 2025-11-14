// SVA binder for sevenseg
`ifndef SEVENSEG_SVA
`define SEVENSEG_SVA

module sevenseg_sva (
  input  logic        clk,
  input  logic        rstn,
  input  logic [7:0]  display_0,
  input  logic [7:0]  display_1,
  input  logic [7:0]  display_2,
  input  logic [7:0]  display_3,
  input  logic [1:0]  decplace,
  input  logic [7:0]  seg,
  input  logic [3:0]  an,
  input  logic [16:0] cnt
);

  function automatic logic [3:0] f_an (input logic [1:0] mux);
    case (mux)
      2'b00: f_an = 4'b0111;
      2'b01: f_an = 4'b1011;
      2'b10: f_an = 4'b1101;
      default: f_an = 4'b1110;
    endcase
  endfunction

  function automatic logic [7:0] f_sel (input logic [1:0] mux,
                                        input logic [7:0] d0, d1, d2, d3);
    case (mux)
      2'b00: f_sel = d0;
      2'b01: f_sel = d1;
      2'b10: f_sel = d2;
      default: f_sel = d3;
    endcase
  endfunction

  function automatic logic [7:0] f_seg (input logic [7:0] ch);
    case (ch)
      8'h20: f_seg = 8'b11111111; // SPACE
      8'h2d: f_seg = 8'b10111111; // HYPHEN
      8'h30: f_seg = 8'b11000000; // 0
      8'h31: f_seg = 8'b11111001; // 1
      8'h32: f_seg = 8'b10100100; // 2
      8'h33: f_seg = 8'b10110000; // 3
      8'h34: f_seg = 8'b10011001; // 4
      8'h35: f_seg = 8'b10010010; // 5
      8'h36: f_seg = 8'b10000010; // 6
      8'h37: f_seg = 8'b11111000; // 7
      8'h38: f_seg = 8'b10000000; // 8
      8'h39: f_seg = 8'b10010000; // 9
      8'h41: f_seg = 8'b10001000; // A
      8'h43: f_seg = 8'b11000110; // C
      8'h45: f_seg = 8'b10000110; // E
      8'h47: f_seg = 8'b10000010; // G
      8'h48: f_seg = 8'b10001001; // H
      8'h4b: f_seg = 8'b10001111; // K
      8'h4c: f_seg = 8'b11000111; // L
      8'h50: f_seg = 8'b10001100; // P
      8'h53: f_seg = 8'b10010010; // S
      8'h5f: f_seg = 8'b11110111; // _
      8'h6f: f_seg = 8'b10100011; // o
      default: f_seg = 8'b11111110; // overline
    endcase
  endfunction

  // Counter behavior
  assert property (@(posedge clk) !rstn |-> cnt == 17'd0);
  assert property (@(posedge clk) rstn && $past(rstn) |-> cnt == $past(cnt) + 17'd1);

  // an decode and integrity
  assert property (@(posedge clk) an == f_an(cnt[16:15]));
  assert property (@(posedge clk) $onehot(~an));
  assert property (@(posedge clk)
                   rstn && $past(rstn) && (cnt[16:15] == $past(cnt[16:15]))
                   |-> an == $past(an));

  // seg decode from selected display byte
  assert property (@(posedge clk)
                   seg == f_seg(f_sel(cnt[16:15], display_0, display_1, display_2, display_3)));

  // Outputs known out of reset
  assert property (@(posedge clk) rstn |-> !$isunknown({an, seg}));

  // decplace has no effect (when other drivers are stable)
  assert property (@(posedge clk)
                   $changed(decplace) && $stable({display_0,display_1,display_2,display_3,cnt[16:15]})
                   |-> $stable({an, seg}));

  // Coverage
  cover property (@(posedge clk) rstn ##1
                  cnt[16:15]==2'b00 ##[1:$] cnt[16:15]==2'b01 ##[1:$]
                  cnt[16:15]==2'b10 ##[1:$] cnt[16:15]==2'b11);

  cover property (@(posedge clk) seg == 8'b11111110); // default path hit
  cover property (@(posedge clk) f_sel(cnt[16:15],display_0,display_1,display_2,display_3)==8'h30 && seg==8'b11000000);
  cover property (@(posedge clk) f_sel(cnt[16:15],display_0,display_1,display_2,display_3)==8'h41 && seg==8'b10001000);
  cover property (@(posedge clk) f_sel(cnt[16:15],display_0,display_1,display_2,display_3)==8'h6f && seg==8'b10100011);

  cover property (@(posedge clk) decplace==2'b00 ##[1:$] decplace==2'b01 ##[1:$] decplace==2'b10 ##[1:$] decplace==2'b11);

endmodule

bind sevenseg sevenseg_sva sva_inst (
  .clk(clk),
  .rstn(rstn),
  .display_0(display_0),
  .display_1(display_1),
  .display_2(display_2),
  .display_3(display_3),
  .decplace(decplace),
  .seg(seg),
  .an(an),
  .cnt(cnt) // internal
);

`endif