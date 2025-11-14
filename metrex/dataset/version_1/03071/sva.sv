// SVA for fifo. Bind this file to the DUT.
//
// Notes:
// - Assumes effective depth 15 (full when 15 elements stored, empty when 0).
// - Uses div domain for FIFO core checks, clk domain for divider/LED checks.

module fifo_sva;

  // Helpers
  function automatic [6:0] enc(input [3:0] v);
    case (v)
      4'h0: enc = reg0; 4'h1: enc = reg1; 4'h2: enc = reg2; 4'h3: enc = reg3;
      4'h4: enc = reg4; 4'h5: enc = reg5; 4'h6: enc = reg6; 4'h7: enc = reg7;
      4'h8: enc = reg8; 4'h9: enc = reg9; 4'ha: enc = rega; 4'hb: enc = regb;
      4'hc: enc = regc; 4'hd: enc = regd; 4'he: enc = rege; 4'hf: enc = regf;
      default: enc = 'x;
    endcase
  endfunction

  wire w_fire = (~wr && ~full_in);
  wire r_fire = (~rd && ~empty_in);

  // Shadow occupancy model (0..15), div-domain reset
  logic [4:0] fifo_cnt;
  always_ff @(posedge div) begin
    if (!rst) fifo_cnt <= '0;
    else unique case ({w_fire,r_fire})
      2'b10: if (fifo_cnt < 5'd15) fifo_cnt <= fifo_cnt + 1;
      2'b01: if (fifo_cnt > 5'd0)  fifo_cnt <= fifo_cnt - 1;
      default:                     fifo_cnt <= fifo_cnt;
    endcase
  end

  // Common disable on active-low reset
  default disable iff (!rst);

  // Reset effects (div domain)
  assert property (@(posedge div) !rst |=> (wp==4'd0 && rp==4'd0 && full_in==1'b0 && empty_in==1'b1));

  // Pointer increment/hold (div domain)
  assert property (@(posedge div) (w_fire) |-> (wp == $past(wp)+4'd1));
  assert property (@(posedge div) (!w_fire) |-> (wp == $past(wp)));
  assert property (@(posedge div) (r_fire) |-> (rp == $past(rp)+4'd1));
  assert property (@(posedge div) (!r_fire) |-> (rp == $past(rp)));

  // No overflow/underflow vs model
  assert property (@(posedge div) (fifo_cnt==5'd15) |-> !w_fire);
  assert property (@(posedge div) (fifo_cnt==5'd0)  |-> !r_fire);

  // Flags match model occupancy
  assert property (@(posedge div) (full_in  == (fifo_cnt==5'd15)));
  assert property (@(posedge div) (empty_in == (fifo_cnt==5'd0)));

  // Full/empty mutually exclusive
  assert property (@(posedge div) !(full_in && empty_in));

  // Pointer difference tracks occupancy (mod-16)
  assert property (@(posedge div) (((wp - rp) & 4'hf) == fifo_cnt[3:0]));

  // Simultaneous read+write keeps occupancy
  assert property (@(posedge div) (w_fire && r_fire) |-> $stable(fifo_cnt));

  // Memory write correctness (address and data)
  assert property (@(posedge div) w_fire |=> mem[$past(wp)] == $past(datain));

  // Write indication (wei) behavior
  assert property (@(posedge div) w_fire |=> wei);
  assert property (@(posedge div) $rose(wei) |-> $past(w_fire));

  // Clock divider correctness (clk domain)
  // When not max, cnt increments and div holds; at max, cnt resets and div toggles
  assert property (@(posedge clk) (cnt != 24'hFFFFFF) |=> (cnt == $past(cnt)+24'd1 && div == $past(div)));
  assert property (@(posedge clk) (cnt == 24'hFFFFFF) |=> (cnt == 24'd0 && div != $past(div)));

  // LED update semantics (clk domain)
  // LED changes only when the LED update block runs
  assert property (@(posedge clk) $changed(led_n) |-> $past(~rd && ~empty_in));
  // When LED block runs, the encoding must match the data path used in that block
  assert property (@(posedge clk) (~rd && ~empty_in) |-> (led_n == enc($past(dataout))));

  // Coverage
  cover property (@(posedge div) (fifo_cnt==5'd0) ##1 w_fire[*15] ##1 full_in);
  cover property (@(posedge div) (fifo_cnt==5'd15) ##1 r_fire[*15] ##1 empty_in);
  cover property (@(posedge div) w_fire && (wp==4'hf) ##1 (wp==4'h0));
  cover property (@(posedge div) r_fire && (rp==4'hf) ##1 (rp==4'h0));
  cover property (@(posedge div) w_fire && r_fire);
  cover property (@(posedge clk) $changed(led_n));

endmodule

bind fifo fifo_sva i_fifo_sva();