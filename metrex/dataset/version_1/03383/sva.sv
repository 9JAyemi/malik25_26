// SVA for KIA
module KIA_sva
(
  input  logic        CLK_I,
  input  logic        RES_I,

  input  logic [0:0]  ADR_I,
  input  logic        WE_I,
  input  logic        CYC_I,
  input  logic        STB_I,
  input  logic        ACK_O,
  input  logic [7:0]  DAT_O,

  input  logic        D_I,
  input  logic        C_I,

  // Internals
  input  logic [3:0]  rp,
  input  logic [3:0]  wp,
  input  logic        ack,
  input  logic [10:0] sr,
  input  logic        cur_C,
  input  logic        prev_C,
  input  logic [3:0]  bits_received,
  input  logic [7:0]  queue [0:15]
);
  default clocking cb @(posedge CLK_I); endclocking
  default disable iff (RES_I);

  // Derived
  logic [3:0] next_wp;            assign next_wp = wp + 4'd1;
  logic       queue_full;         assign queue_full  = (next_wp == rp);
  logic       queue_empty;        assign queue_empty = (rp == wp);

  logic kqstat_addressed;         assign kqstat_addressed = (ADR_I == 1'b0) && ack && !WE_I;
  logic kqdata_addressed;         assign kqdata_addressed = (ADR_I == 1'b1) && ack && !WE_I;
  logic kqpop_addressed;          assign kqpop_addressed  = (ADR_I == 1'b1) && ack &&  WE_I && !queue_empty;

  logic ps2clk_edge;              assign ps2clk_edge = (!cur_C) && prev_C;
  logic waiting_for_start_bit;    assign waiting_for_start_bit = (bits_received == 4'd0);
  logic waiting_for_stop_bit;     assign waiting_for_stop_bit  = (bits_received == 4'd10);
  logic is_start_bit;             assign is_start_bit = (D_I == 1'b0);
  logic is_stop_bit;              assign is_stop_bit  = (D_I == 1'b1);

  // Bus / ACK
  assert property (ack == $past(CYC_I & STB_I));
  assert property (ACK_O == ack);
  assert property ((ack && !WE_I) |-> (kqstat_addressed ^ kqdata_addressed));

  // Read data/status correctness
  assert property (kqstat_addressed |-> DAT_O == {6'h00, queue_full, queue_empty});
  assert property (kqdata_addressed |-> DAT_O == queue[rp]);

  // FIFO pop pointer behavior
  assert property (kqpop_addressed |-> rp == $past(rp) + 4'd1);
  assert property (!kqpop_addressed |-> rp == $past(rp));

  // Reset effects (observed next cycle)
  assert property (RES_I |=> rp == 4'd0);
  assert property (RES_I |=> ack == 1'b0);
  assert property (RES_I |=> (sr == 11'h7FF) && (prev_C == 1'b1) && (cur_C == 1'b1) && (bits_received == 4'd0) && (wp == 4'd0));

  // PS/2 sampler sequencing
  assert property (prev_C == $past(cur_C));
  assert property (bits_received <= 4'd10);

  assert property (ps2clk_edge && waiting_for_start_bit && is_start_bit
                   |=> bits_received == $past(bits_received) + 4'd1);
  assert property (ps2clk_edge && !waiting_for_stop_bit && !waiting_for_start_bit
                   |=> bits_received == $past(bits_received) + 4'd1);

  // Stop bit handling and FIFO write
  assert property (ps2clk_edge && waiting_for_stop_bit && is_stop_bit && !queue_full
                   |=> (wp == $past(wp) + 4'd1) && (bits_received == 4'd0) && (queue[$past(wp)] == $past(sr[9:2])));
  assert property (ps2clk_edge && waiting_for_stop_bit && is_stop_bit && queue_full
                   |=> (wp == $past(wp)) && (bits_received == 4'd0));
  assert property (ps2clk_edge && waiting_for_stop_bit && !is_stop_bit
                   |=> bits_received == $past(bits_received));

  // wp only advances on accepted stop bit (outside reset)
  assert property (!(ps2clk_edge && waiting_for_stop_bit && is_stop_bit && !queue_full)
                   |-> wp == $past(wp));

  // Coverage
  cover property (CYC_I && STB_I ##1 ack);
  cover property (ack && !WE_I && (ADR_I == 1'b0));
  cover property (ack && !WE_I && (ADR_I == 1'b1));
  cover property (ack &&  WE_I && (ADR_I == 1'b1) && !queue_empty);

  cover property (ps2clk_edge && waiting_for_start_bit && is_start_bit
                  ##[1:12] ps2clk_edge && waiting_for_stop_bit && is_stop_bit && !queue_full);

  cover property (queue_full && ps2clk_edge && waiting_for_stop_bit && is_stop_bit);
  cover property (queue_empty ##1 !queue_empty);
  cover property (!queue_empty ##1 queue_empty);

  cover property (kqpop_addressed && ps2clk_edge && waiting_for_stop_bit && is_stop_bit && !queue_full);

  cover property ((wp == 4'hF) && ps2clk_edge && waiting_for_stop_bit && is_stop_bit && !queue_full ##1 (wp == 4'h0));
  cover property ((rp == 4'hF) && kqpop_addressed ##1 (rp == 4'h0));
endmodule

bind KIA KIA_sva sva (
  .CLK_I(CLK_I),
  .RES_I(RES_I),

  .ADR_I(ADR_I),
  .WE_I(WE_I),
  .CYC_I(CYC_I),
  .STB_I(STB_I),
  .ACK_O(ACK_O),
  .DAT_O(DAT_O),

  .D_I(D_I),
  .C_I(C_I),

  .rp(rp),
  .wp(wp),
  .ack(ack),
  .sr(sr),
  .cur_C(cur_C),
  .prev_C(prev_C),
  .bits_received(bits_received),
  .queue(queue)
);