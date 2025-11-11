// SVA for axi_traffic_gen_v2_0_7_id_track
// Concise checks + coverage on push/clear/search/free logic.
// Bind this file to the DUT.

module axi_traffic_gen_v2_0_7_id_track_sva
  #(parameter int ID_WIDTH = 1)
(
  input  logic                  Clk,
  input  logic                  rst_l,
  // DUT I/O
  input  logic [ID_WIDTH-1:0]   in_push_id,
  input  logic                  in_push,
  input  logic [ID_WIDTH-1:0]   in_search_id,
  input  logic [3:0]            in_clear_pos,
  input  logic                  in_only_entry0,
  input  logic [3:0]            out_push_pos,
  input  logic [3:0]            out_search_hit,
  input  logic [3:0]            out_free,
  // DUT internals
  input  logic [ID_WIDTH:0]     id_arr0_ff,
  input  logic [ID_WIDTH:0]     id_arr1_ff,
  input  logic [ID_WIDTH:0]     id_arr2_ff,
  input  logic [ID_WIDTH:0]     id_arr3_ff,
  input  logic [3:0]            push_pos_ff,
  input  logic [3:0]            push_pos_2ff,
  input  logic [3:0]            in_clear_pos_ff,
  input  logic [ID_WIDTH:0]     push_id,
  input  logic [ID_WIDTH:0]     search_id,
  input  logic [3:0]            push_search,
  input  logic [3:0]            free_pre,
  input  logic [3:0]            free,
  input  logic [3:0]            first_free,
  input  logic [3:0]            push_pos,
  input  logic [3:0]            search_pos,
  input  logic [3:0]            do_clear
);

  localparam int MSB = ID_WIDTH;

  default clocking cb @(posedge Clk); endclocking
  default disable iff (!rst_l)

  // Pack arrays for concise per-slot properties
  logic [ID_WIDTH:0] id_ff [3:0];
  assign id_ff[0]=id_arr0_ff;
  assign id_ff[1]=id_arr1_ff;
  assign id_ff[2]=id_arr2_ff;
  assign id_ff[3]=id_arr3_ff;

  // Reset behavior (checked outside disable)
  assert property (@(posedge Clk) !rst_l |=> (id_arr0_ff=='0 && id_arr1_ff=='0 && id_arr2_ff=='0 && id_arr3_ff=='0
                                              && push_pos_ff==4'h0 && push_pos_2ff==4'h0 && in_clear_pos_ff==4'h0));

  // Pipeline registers
  assert property (push_pos_ff     == $past(push_pos));
  assert property (push_pos_2ff    == $past(push_pos_ff));
  assert property (in_clear_pos_ff == $past(in_clear_pos));

  // Free vector correctness and gating
  assert property (free_pre == {~id_arr3_ff[MSB], ~id_arr2_ff[MSB], ~id_arr1_ff[MSB], ~id_arr0_ff[MSB]});
  assert property ( in_only_entry0 |-> (out_free[3:1]==3'b000 && out_free[0]==free_pre[0]));
  assert property (!in_only_entry0 |-> (out_free==free_pre));

  // first_free priority and onehot0
  assert property (free[0]                                   |-> first_free==4'h1);
  assert property (!free[0] &&  free[1]                      |-> first_free==4'h2);
  assert property (!free[0] && !free[1] &&  free[2]          |-> first_free==4'h4);
  assert property (!free[0] && !free[1] && !free[2] && free[3] |-> first_free==4'h8);
  assert property (free==4'h0 |-> first_free==4'h0);
  assert property ($onehot0(first_free));

  // push_pos selection
  assert property (!in_push |-> push_pos==4'h0);
  assert property ( in_push && (push_search!=4'h0)            |-> push_pos==push_search);
  assert property ( in_push && (push_search==4'h0) && (free!=4'h0) |-> push_pos==first_free);
  assert property ( in_push && (push_search==4'h0) && (free==4'h0) |-> push_pos==4'h0);

  // Search result correctness
  assert property (out_search_hit == { (search_id==id_arr3_ff),
                                       (search_id==id_arr2_ff),
                                       (search_id==id_arr1_ff),
                                       (search_id==id_arr0_ff) });

  // Out ports reflect internal wires
  assert property (out_push_pos==push_pos);
  assert property (out_free==free);

  // Per-slot state update rules
  genvar i;
  generate
    for (i=0;i<4;i++) begin: G_ID_SLOTS
      // Push into slot writes full ID (including valid=1)
      assert property (push_pos[i] |=> id_ff[i]==push_id);

      // Clear (when allowed) only clears valid bit, preserves ID bits
      assert property (!push_pos[i] && (~push_pos_ff[i] && ~push_pos_2ff[i] && in_clear_pos_ff[i])
                       |=> (id_ff[i][MSB]==1'b0 && id_ff[i][MSB-1:0]==$past(id_ff[i][MSB-1:0])));

      // Otherwise hold value
      assert property (!push_pos[i] && !(~push_pos_ff[i] && ~push_pos_2ff[i] && in_clear_pos_ff[i])
                       |=> id_ff[i]==$past(id_ff[i]));
    end
  endgenerate

  // ------------- Coverage -------------

  // Pushes into each slot
  cover property (in_push && push_pos==4'h1);
  cover property (in_push && push_pos==4'h2);
  cover property (in_push && push_pos==4'h4);
  cover property (in_push && push_pos==4'h8);

  // Push hits existing ID (match)
  cover property (in_push && (push_search!=4'h0) && (push_pos==push_search));

  // Fill all entries -> free==0, then a blocked push
  cover property (free==4'h0);
  cover property (free==4'h0 ##1 (in_push && push_pos==4'h0));

  // Clear occurs (per slot) and is suppressed by recent pushes
  cover property ((~push_pos_ff[0] && ~push_pos_2ff[0] && in_clear_pos_ff[0]) ##1 (id_arr0_ff[MSB]==1'b0));
  cover property (( push_pos_ff[0] ||  push_pos_2ff[0]) && in_clear_pos_ff[0] && !push_pos[0]);

  // in_only_entry0 gating observed
  cover property (in_only_entry0 && (free_pre!=4'h0) && (out_free=={3'b000,free_pre[0]}));

  // Search hits each slot
  cover property (out_search_hit==4'h1);
  cover property (out_search_hit==4'h2);
  cover property (out_search_hit==4'h4);
  cover property (out_search_hit==4'h8);

endmodule

bind axi_traffic_gen_v2_0_7_id_track
  axi_traffic_gen_v2_0_7_id_track_sva #(.ID_WIDTH(ID_WIDTH)) i_axi_traffic_gen_v2_0_7_id_track_sva
  (
    .Clk(Clk),
    .rst_l(rst_l),
    .in_push_id(in_push_id),
    .in_push(in_push),
    .in_search_id(in_search_id),
    .in_clear_pos(in_clear_pos),
    .in_only_entry0(in_only_entry0),
    .out_push_pos(out_push_pos),
    .out_search_hit(out_search_hit),
    .out_free(out_free),
    .id_arr0_ff(id_arr0_ff),
    .id_arr1_ff(id_arr1_ff),
    .id_arr2_ff(id_arr2_ff),
    .id_arr3_ff(id_arr3_ff),
    .push_pos_ff(push_pos_ff),
    .push_pos_2ff(push_pos_2ff),
    .in_clear_pos_ff(in_clear_pos_ff),
    .push_id(push_id),
    .search_id(search_id),
    .push_search(push_search),
    .free_pre(free_pre),
    .free(free),
    .first_free(first_free),
    .push_pos(push_pos),
    .search_pos(search_pos),
    .do_clear(do_clear)
  );