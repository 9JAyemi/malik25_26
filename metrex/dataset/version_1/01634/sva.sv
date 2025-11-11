// SVA for precision_dac
// Bind into DUT; uses internal regs for strong checking

module precision_dac_sva #(parameter CLK_DIV=3) ();

  // Default clock
  default clocking cb @ (posedge clk); endclocking

  // Shorthands
  let LAST0 = {1'b0, {(CLK_DIV-1){1'b1}}};    // value that raises sclk
  let ALL1  = {CLK_DIV{1'b1}};                // value that lowers sclk
  let at_pulse = valid && (cnt_clk == LAST0); // base-tick where sclk<=1 and cnt_sclk steps
  let at_fall  = valid && (cnt_clk == ALL1);  // base-tick where sclk<=0
  let gate     = (sync == 1'b0) || (cnt_sclk[4:0] == 5'b00000);
  let hdr0     = (cnt_sclk[4:2] == 3'b000);
  let hdr1     = (cnt_sclk[4:2] == 3'b001);
  let endp     = (cnt_sclk[4:0] == 5'b11000);
  let group    = cnt_sclk[6:5];

  // Idle defaults when valid is low
  assert property (!valid |-> (cnt_clk==0 && cnt_sclk==0 && sync==1 && sdi==0 && ldac==0 && sclk==0));

  // cnt_clk stepping behavior under valid
  assert property ($rose(valid) |-> cnt_clk == 'd1);
  assert property (valid && $past(valid) |-> cnt_clk == $past(cnt_clk) + 1);

  // sclk can only change at the two programmed cnt_clk values
  assert property ($rose(sclk) |-> at_pulse);
  assert property ($fell(sclk) |-> at_fall);
  assert property (valid && !(cnt_clk==LAST0 || cnt_clk==ALL1) |-> sclk == $past(sclk));

  // cnt_sclk increments only on the sclk-raise base tick
  assert property (valid && (cnt_clk==LAST0) |-> cnt_sclk == $past(cnt_sclk) + 1);
  assert property (valid && !(cnt_clk==LAST0) |-> cnt_sclk == $past(cnt_sclk));

  // Latching of cmd_reg/data_reg and LDAC high at frame start
  assert property (at_pulse && (cnt_sclk==7'd0) |=> (ldac==1 && cmd_reg==$past(cmd) && data_reg==$past(data)));
  // cmd_reg/data_reg stable otherwise
  assert property (valid && !(at_pulse && (cnt_sclk==7'd0)) |-> cmd_reg == $past(cmd_reg));
  assert property (valid && !(at_pulse && (cnt_sclk==7'd0)) |-> data_reg == $past(data_reg));

  // SYNC low at start-of-frame (LSBs==00000), stays low until endpoint (11000), then high
  sequence start_frame; at_pulse && (cnt_sclk[4:0]==5'b00000); endsequence
  sequence end_frame;   at_pulse && endp;                      endsequence
  assert property (start_frame |=> sync==0);
  assert property (start_frame |-> (sync==0 until end_frame) ##1 sync==1);

  // LDAC deasserted low at endpoint when group==3
  assert property (end_frame && (group==2'd3) |=> ldac==0);
  // LDAC only changes at start or (endpoint && group==3)
  assert property ($changed(ldac) |-> (at_pulse && ((cnt_sclk==7'd0) || (endp && group==2'd3))));

  // SYNC only changes at start or endpoint
  assert property ($changed(sync) |-> (at_pulse && ((cnt_sclk[4:0]==5'b00000) || endp)));

  // SDI updates only on gated sclk-raise ticks (and not on endpoint)
  assert property (valid && !(at_pulse && gate && !endp) |-> sdi == $past(sdi));

  // SDI header: first 4 bits are cmd[3:0] MSB-first when hdr0
  assert property (at_pulse && gate && hdr0 |=> sdi == $past(cmd[3 - cnt_sclk[1:0]]));

  // SDI header: next 4 bits equal (cnt_sclk[6:5] == ~cnt_sclk[1:0]) when hdr1
  assert property (at_pulse && gate && hdr1 |=> sdi == $past(cnt_sclk[6:5] == ~cnt_sclk[1:0]));

  // SDI payload: for LSB in 8..23, drive data_reg MSB-first per group
  assert property (at_pulse && gate && !(hdr0 || hdr1 || endp)
                   |=> sdi == $past(data_reg[16*cnt_sclk[6:5] + (23 - cnt_sclk[4:0])]));

  // Basic progress cover: see a full frame with LDAC drop at group 3
  cover property ($rose(valid)
                  ##[1:$] start_frame
                  ##[1:$] (at_pulse && endp && group==2'd3)
                  ##1 (ldac==0 && sync==1));

  // Cover endpoint seen for each group 0..3
  genvar g;
  generate
    for (g=0; g<4; g++) begin : C_GRP
      cover property (valid ##[1:$] (at_pulse && endp && (group==g)));
    end
  endgenerate

endmodule

bind precision_dac precision_dac_sva #(.CLK_DIV(CLK_DIV)) sva();