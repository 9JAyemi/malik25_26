// SVA for fifo. Binds into DUT scope to see internals.
// Concise checks for clock divider, pointers, memory, flags, 7-seg, and coverage.

bind fifo fifo_sva u_fifo_sva();

module fifo_sva;

  // ---------- Constants / helpers ----------
  localparam [23:0] MAX24 = 24'hFF_FFFF;

  function automatic [6:0] seg_map (input [3:0] v);
    case (v)
      4'h0: seg_map = 7'b0000001;
      4'h1: seg_map = 7'b1001111;
      4'h2: seg_map = 7'b0010010;
      4'h3: seg_map = 7'b0000110;
      4'h4: seg_map = 7'b1001100;
      4'h5: seg_map = 7'b0100100;
      4'h6: seg_map = 7'b0100000;
      4'h7: seg_map = 7'b0001101;
      4'h8: seg_map = 7'b0000000;
      4'h9: seg_map = 7'b0000100;
      4'hA: seg_map = 7'b0001000;
      4'hB: seg_map = 7'b1100000;
      4'hC: seg_map = 7'b0110001;
      4'hD: seg_map = 7'b1000010;
      4'hE: seg_map = 7'b0110000;
      4'hF: seg_map = 7'b0111000;
      default: seg_map = 7'hxx;
    endcase
  endfunction

  function automatic bit near_full(input [3:0] wp_i, rp_i);
    return (wp_i == rp_i - 1) || (rp_i == 4'h0 && wp_i == 4'hF);
  endfunction

  function automatic bit near_empty(input [3:0] rp_i, wp_i);
    return (rp_i == wp_i - 1) || (rp_i == 4'hF && wp_i == 4'h0);
  endfunction

  // ---------- clk-domain: divider/counter and output passthru ----------
  a_div_toggle_on_wrap: assert property (@(posedge clk) (cnt==MAX24) |-> (div != $past(div)));
  a_div_hold_not_wrap : assert property (@(posedge clk) (cnt!=MAX24) |-> (div == $past(div)));
  a_cnt_inc           : assert property (@(posedge clk) (cnt!=MAX24) |-> (cnt == $past(cnt)+1));
  a_cnt_wrap          : assert property (@(posedge clk) (cnt==MAX24) |-> (cnt == '0));

  // Outputs mirror internals; wei always zero after reset deasserts (rst is active-low)
  a_out_passthru: assert property (@(posedge clk) full==full_in && empty==empty_in && wei==wei_in);
  a_wei_zero    : assert property (@(posedge clk) disable iff (!rst) wei==1'b0 && wei_in==1'b0);

  // ---------- div-domain: reset effects ----------
  a_rst_state: assert property (@(posedge div)
                      !rst |-> ##1 (wp==4'h0 && rp==4'h0 && full_in==1'b0 && empty_in==1'b1));

  // ---------- div-domain: pointer updates ----------
  a_wp_inc : assert property (@(posedge div) disable iff (!rst)
                      (~wr && ~full_in) |-> (wp == $past(wp)+1));
  a_wp_hold: assert property (@(posedge div) disable iff (!rst)
                      !(~wr && ~full_in) |-> (wp == $past(wp)));

  a_rp_inc : assert property (@(posedge div) disable iff (!rst)
                      (~rd && ~empty_in) |-> (rp == $past(rp)+1));
  a_rp_hold: assert property (@(posedge div) disable iff (!rst)
                      !(~rd && ~empty_in) |-> (rp == $past(rp)));

  // ---------- div-domain: memory semantics ----------
  // Write takes effect one div cycle later at the old wp
  a_mem_write: assert property (@(posedge div) disable iff (!rst)
                      $past(~wr && ~full_in) |-> (mem[$past(wp)] == $past(datain)));
  // No write when full
  a_no_write_when_full: assert property (@(posedge div) disable iff (!rst)
                      (~wr && full_in) |-> ($stable(wp) && $stable(mem[wp])));

  // Read timing: dataout captures prior mem[rp] one cycle after read
  a_read_dataout: assert property (@(posedge div) disable iff (!rst)
                      $past(~rd && ~empty_in) |-> (dataout == $past(mem[rp])));
  // No read effect when empty
  a_no_read_when_empty: assert property (@(posedge div) disable iff (!rst)
                      (~rd && empty_in) |-> $stable(dataout));

  // ---------- div-domain: flags per RTL ----------
  a_full_set  : assert property (@(posedge div) disable iff (!rst)
                      (rd && ~wr && near_full(wp,rp)) |-> ##1 full_in);
  a_full_clr  : assert property (@(posedge div) disable iff (!rst)
                      (full_in && ~rd) |-> ##1 !full_in);

  a_empty_set : assert property (@(posedge div) disable iff (!rst)
                      (~rd && wr && near_empty(rp,wp)) |-> ##1 empty_in);
  a_empty_clr : assert property (@(posedge div) disable iff (!rst)
                      (empty_in && ~wr) |-> ##1 !empty_in);

  // Never both full and empty after reset deasserted
  a_not_full_and_empty: assert property (@(posedge div) disable iff (!rst)
                      !(full && empty));

  // ---------- 7-seg output ----------
  // LED always reflects current dataout table
  a_led_map: assert property (@(posedge div) led_n == seg_map(dataout));

  // ---------- Sanity: no Xs on key signals after reset ----------
  a_no_x: assert property (@(posedge div) disable iff (!rst)
                      !$isunknown({full, empty, led_n, dataout, wp, rp, div}));

  // ---------- Coverage ----------
  c_write     : cover property (@(posedge div) disable iff (!rst) (~wr && ~full_in));
  c_read      : cover property (@(posedge div) disable iff (!rst) (~rd && ~empty_in));
  c_full_hit  : cover property (@(posedge div) disable iff (!rst)
                      (rd && ~wr && near_full(wp,rp)) ##1 full_in);
  c_empty_hit : cover property (@(posedge div) disable iff (!rst)
                      (~rd && wr && near_empty(rp,wp)) ##1 empty_in);
  c_wp_wrap   : cover property (@(posedge div) disable iff (!rst)
                      (wp==4'hF && ~wr && ~full_in) ##1 (wp==4'h0));
  c_rp_wrap   : cover property (@(posedge div) disable iff (!rst)
                      (rp==4'hF && ~rd && ~empty_in) ##1 (rp==4'h0));

  // 7-seg values coverage
  covergroup cg_led @(posedge div);
    cp_led: coverpoint led_n {
      bins b0  = {7'b0000001};
      bins b1  = {7'b1001111};
      bins b2  = {7'b0010010};
      bins b3  = {7'b0000110};
      bins b4  = {7'b1001100};
      bins b5  = {7'b0100100};
      bins b6  = {7'b0100000};
      bins b7  = {7'b0001101};
      bins b8  = {7'b0000000};
      bins b9  = {7'b0000100};
      bins bA  = {7'b0001000};
      bins bB  = {7'b1100000};
      bins bC  = {7'b0110001};
      bins bD  = {7'b1000010};
      bins bE  = {7'b0110000};
      bins bF  = {7'b0111000};
    }
  endgroup
  cg_led cg_led_i = new();

endmodule