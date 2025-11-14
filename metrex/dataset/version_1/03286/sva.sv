// SVA checker for arbiter_2_masters
// Bind this checker after compiling the DUT.

module arbiter_2_masters_sva
(
  input           clk,
  input           rst,

  input           i_m0_we,
  input           i_m0_cyc,
  input           i_m0_stb,
  input   [3:0]   i_m0_sel,
  input   [31:0]  i_m0_dat,
  input   [31:0]  i_m0_adr,
  input           o_m0_ack,
  input   [31:0]  o_m0_dat,
  input           o_m0_int,

  input           i_m1_we,
  input           i_m1_cyc,
  input           i_m1_stb,
  input   [3:0]   i_m1_sel,
  input   [31:0]  i_m1_dat,
  input   [31:0]  i_m1_adr,
  input           o_m1_ack,
  input   [31:0]  o_m1_dat,
  input           o_m1_int,

  input           o_s_we,
  input           o_s_stb,
  input           o_s_cyc,
  input   [3:0]   o_s_sel,
  input   [31:0]  o_s_adr,
  input   [31:0]  o_s_dat,
  input   [31:0]  i_s_dat,
  input           i_s_ack,
  input           i_s_int,

  // internal DUT state
  input   [7:0]   master_select,
  input   [7:0]   priority_select
);

  localparam [7:0] MASTER_NO_SEL = 8'hFF;
  localparam [7:0] MASTER_0      = 8'd0;
  localparam [7:0] MASTER_1      = 8'd1;

  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Reset drives known idle state
  assert property (rst |-> master_select == MASTER_NO_SEL && priority_select == MASTER_NO_SEL);

  // Encodings remain within legal set
  assert property (master_select inside {MASTER_NO_SEL,MASTER_0,MASTER_1});
  assert property (priority_select inside {MASTER_NO_SEL,MASTER_0,MASTER_1});

  // Data path duplication to masters
  assert property (o_m0_dat == i_s_dat);
  assert property (o_m1_dat == i_s_dat);

  // Ack/int routing exclusivity and correctness
  assert property (o_m0_ack & o_m1_ack |-> 0); // mutually exclusive
  assert property (o_m0_int & o_m1_int |-> 0); // mutually exclusive

  // No selection -> all outputs to slave idle; acks/ints deasserted
  assert property (master_select == MASTER_NO_SEL |->
                   !o_s_we && !o_s_stb && !o_s_cyc &&
                   o_s_sel == 4'h0 && o_s_adr == 32'h0 && o_s_dat == 32'h0 &&
                   !o_m0_ack && !o_m1_ack && !o_m0_int && !o_m1_int);

  // M0 selected -> strict muxing and routing
  assert property (master_select == MASTER_0 |->
                   o_s_we  == i_m0_we  &&
                   o_s_stb == i_m0_stb &&
                   o_s_cyc == i_m0_cyc &&
                   o_s_sel == i_m0_sel &&
                   o_s_adr == i_m0_adr &&
                   o_s_dat == i_m0_dat &&
                   o_m0_ack == i_s_ack && !o_m1_ack &&
                   o_m0_int == i_s_int && !o_m1_int);

  // M1 selected -> strict muxing and routing
  assert property (master_select == MASTER_1 |->
                   o_s_we  == i_m1_we  &&
                   o_s_stb == i_m1_stb &&
                   o_s_cyc == i_m1_cyc &&
                   o_s_sel == i_m1_sel &&
                   o_s_adr == i_m1_adr &&
                   o_s_dat == i_m1_dat &&
                   o_m1_ack == i_s_ack && !o_m0_ack &&
                   o_m1_int == i_s_int && !o_m0_int);

  // Priority tracking from requests (sampled each cycle)
  assert property (i_m0_cyc |=> priority_select == MASTER_0);
  assert property (!i_m0_cyc && i_m1_cyc |=> priority_select == MASTER_1);
  assert property (!i_m0_cyc && !i_m1_cyc |=> priority_select == MASTER_NO_SEL);

  // Idle grants: deterministic choice when idle
  assert property (master_select == MASTER_NO_SEL &&  i_m0_cyc && !i_m1_cyc |=> master_select == MASTER_0);
  assert property (master_select == MASTER_NO_SEL && !i_m0_cyc &&  i_m1_cyc |=> master_select == MASTER_1);
  assert property (master_select == MASTER_NO_SEL &&  i_m0_cyc &&  i_m1_cyc |=> master_select == MASTER_0);

  // No direct switch between masters without passing through NO_SEL
  assert property ($past(master_select) == MASTER_0 && master_select == MASTER_1 |-> 0);
  assert property ($past(master_select) == MASTER_1 && master_select == MASTER_0 |-> 0);

  // Selection is held during ACK
  assert property (i_s_ack |=> master_select == $past(master_select));

  // Release conditions: Only allowed reasons to drop selection
  assert property ($past(master_select) == MASTER_0 && master_select == MASTER_NO_SEL |->
                   !$past(i_s_ack) && !$past(i_m0_cyc));

  assert property ($past(master_select) == MASTER_1 && master_select == MASTER_NO_SEL |->
                   !$past(i_s_ack) && ( !$past(i_m1_cyc) ||
                                        ($past(priority_select) == MASTER_0 && !$past(o_s_stb)) ));

  // Coverage
  cover property (master_select == MASTER_NO_SEL ##1 master_select == MASTER_0);
  cover property (master_select == MASTER_NO_SEL ##1 master_select == MASTER_1);
  cover property (master_select == MASTER_0 && i_s_ack);
  cover property (master_select == MASTER_1 && i_s_ack);
  cover property (master_select == MASTER_1 && priority_select == MASTER_0 && !o_s_stb && !i_s_ack ##1
                  master_select == MASTER_NO_SEL ##1 master_select == MASTER_0);

endmodule

bind arbiter_2_masters arbiter_2_masters_sva
(
  .clk(clk),
  .rst(rst),

  .i_m0_we(i_m0_we),
  .i_m0_cyc(i_m0_cyc),
  .i_m0_stb(i_m0_stb),
  .i_m0_sel(i_m0_sel),
  .i_m0_dat(i_m0_dat),
  .i_m0_adr(i_m0_adr),
  .o_m0_ack(o_m0_ack),
  .o_m0_dat(o_m0_dat),
  .o_m0_int(o_m0_int),

  .i_m1_we(i_m1_we),
  .i_m1_cyc(i_m1_cyc),
  .i_m1_stb(i_m1_stb),
  .i_m1_sel(i_m1_sel),
  .i_m1_dat(i_m1_dat),
  .i_m1_adr(i_m1_adr),
  .o_m1_ack(o_m1_ack),
  .o_m1_dat(o_m1_dat),
  .o_m1_int(o_m1_int),

  .o_s_we(o_s_we),
  .o_s_stb(o_s_stb),
  .o_s_cyc(o_s_cyc),
  .o_s_sel(o_s_sel),
  .o_s_adr(o_s_adr),
  .o_s_dat(o_s_dat),
  .i_s_dat(i_s_dat),
  .i_s_ack(i_s_ack),
  .i_s_int(i_s_int),

  .master_select(master_select),
  .priority_select(priority_select)
);