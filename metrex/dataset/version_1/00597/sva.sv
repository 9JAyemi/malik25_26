// SVA for arbiter_2_masters
// Bindable, concise, checks key behavior and coverage

module arbiter_2_masters_sva
(
  input               clk,
  input               rst,

  input               i_m0_we,
  input               i_m0_cyc,
  input               i_m0_stb,
  input       [3:0]   i_m0_sel,
  input       [31:0]  i_m0_dat,
  input       [31:0]  i_m0_adr,

  input               i_m1_we,
  input               i_m1_cyc,
  input               i_m1_stb,
  input       [3:0]   i_m1_sel,
  input       [31:0]  i_m1_dat,
  input       [31:0]  i_m1_adr,

  output              o_m0_ack,
  output      [31:0]  o_m0_dat,
  output              o_m0_int,

  output              o_m1_ack,
  output      [31:0]  o_m1_dat,
  output              o_m1_int,

  output              o_s_we,
  output              o_s_stb,
  output              o_s_cyc,
  output      [3:0]   o_s_sel,
  output      [31:0]  o_s_adr,
  output      [31:0]  o_s_dat,

  input       [31:0]  i_s_dat,
  input               i_s_ack,
  input               i_s_int,

  input       [7:0]   master_select,
  input       [7:0]   priority_select
);

  localparam [7:0] MASTER_NO_SEL = 8'hFF;
  localparam [7:0] MASTER_0      = 8'd0;
  localparam [7:0] MASTER_1      = 8'd1;

  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // past-valid guard for $past usage
  logic past_valid;
  always @(posedge clk) if (rst) past_valid <= 1'b0; else past_valid <= 1'b1;

  // Reset initializes selects
  assert property (@(posedge clk) rst |=> master_select==MASTER_NO_SEL && priority_select==MASTER_NO_SEL);

  // State legality
  assert property (master_select  inside {MASTER_NO_SEL, MASTER_0, MASTER_1});
  assert property (priority_select inside {MASTER_NO_SEL, MASTER_0, MASTER_1});

  // Slave output mapping
  assert property (master_select==MASTER_NO_SEL |-> o_s_we==0 && o_s_stb==0 && o_s_cyc==0
                                         && o_s_sel==4'b0 && o_s_adr==32'b0 && o_s_dat==32'b0);
  assert property (master_select==MASTER_0 |-> o_s_we==i_m0_we && o_s_stb==i_m0_stb && o_s_cyc==i_m0_cyc
                                        && o_s_sel==i_m0_sel && o_s_adr==i_m0_adr && o_s_dat==i_m0_dat);
  assert property (master_select==MASTER_1 |-> o_s_we==i_m1_we && o_s_stb==i_m1_stb && o_s_cyc==i_m1_cyc
                                        && o_s_sel==i_m1_sel && o_s_adr==i_m1_adr && o_s_dat==i_m1_dat);

  // Return-path mapping
  assert property (o_m0_ack == (master_select==MASTER_0 && i_s_ack));
  assert property (o_m1_ack == (master_select==MASTER_1 && i_s_ack));
  assert property (o_m0_int == (master_select==MASTER_0 && i_s_int));
  assert property (o_m1_int == (master_select==MASTER_1 && i_s_int));
  assert property (o_m0_dat == i_s_dat);
  assert property (o_m1_dat == i_s_dat);

  // Arbitration: acquire from idle
  assert property (master_select==MASTER_NO_SEL && i_m0_cyc           |=> master_select==MASTER_0);
  assert property (master_select==MASTER_NO_SEL && !i_m0_cyc && i_m1_cyc |=> master_select==MASTER_1);
  assert property (master_select==MASTER_NO_SEL && i_m0_cyc && i_m1_cyc |=> master_select==MASTER_0);

  // Deselect on end of cycle (no ack)
  assert property (master_select==MASTER_0 && !i_m0_cyc && !i_s_ack |=> master_select==MASTER_NO_SEL);
  assert property (master_select==MASTER_1 && !i_m1_cyc && !i_s_ack |=> master_select==MASTER_NO_SEL);

  // Preemption rule (M1 yields to M0 when idle on bus)
  assert property (master_select==MASTER_1 && priority_select==MASTER_0 && !o_s_stb && !i_s_ack
                   |=> master_select==MASTER_NO_SEL);

  // No direct master-to-master switch (must pass through NO_SEL)
  assert property (past_valid |-> !($past(master_select)==MASTER_0 && master_select==MASTER_1)
                               && !($past(master_select)==MASTER_1 && master_select==MASTER_0));

  // Coverage
  cover property (rst ##1 master_select==MASTER_NO_SEL);
  cover property (master_select==MASTER_NO_SEL && i_m0_cyc |=> master_select==MASTER_0);
  cover property (master_select==MASTER_NO_SEL && !i_m0_cyc && i_m1_cyc |=> master_select==MASTER_1);
  cover property (master_select==MASTER_NO_SEL && i_m0_cyc && i_m1_cyc |=> master_select==MASTER_0);
  cover property (master_select==MASTER_0 && i_s_ack && o_m0_ack);
  cover property (master_select==MASTER_1 && i_s_ack && o_m1_ack);
  cover property (master_select==MASTER_0 && !i_m0_cyc && !i_s_ack |=> master_select==MASTER_NO_SEL);
  cover property (master_select==MASTER_1 && !i_m1_cyc && !i_s_ack |=> master_select==MASTER_NO_SEL);
  cover property (master_select==MASTER_1 && priority_select==MASTER_0 && !o_s_stb && !i_s_ack
                  |=> master_select==MASTER_NO_SEL);
endmodule

bind arbiter_2_masters arbiter_2_masters_sva sva_i (
  .clk(clk), .rst(rst),
  .i_m0_we(i_m0_we), .i_m0_cyc(i_m0_cyc), .i_m0_stb(i_m0_stb), .i_m0_sel(i_m0_sel), .i_m0_dat(i_m0_dat), .i_m0_adr(i_m0_adr),
  .i_m1_we(i_m1_we), .i_m1_cyc(i_m1_cyc), .i_m1_stb(i_m1_stb), .i_m1_sel(i_m1_sel), .i_m1_dat(i_m1_dat), .i_m1_adr(i_m1_adr),
  .o_m0_ack(o_m0_ack), .o_m0_dat(o_m0_dat), .o_m0_int(o_m0_int),
  .o_m1_ack(o_m1_ack), .o_m1_dat(o_m1_dat), .o_m1_int(o_m1_int),
  .o_s_we(o_s_we), .o_s_stb(o_s_stb), .o_s_cyc(o_s_cyc), .o_s_sel(o_s_sel), .o_s_adr(o_s_adr), .o_s_dat(o_s_dat),
  .i_s_dat(i_s_dat), .i_s_ack(i_s_ack), .i_s_int(i_s_int),
  .master_select(master_select), .priority_select(priority_select)
);