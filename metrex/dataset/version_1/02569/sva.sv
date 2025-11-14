// SVA for module queue
// Bindable, concise, and checks control, flags, pointers, and key datapath behaviors.

module queue_sva #(
  parameter int WIDTH  = 108,
  parameter int LENGTH = 4
)(
  input  logic              GCLK,
  input  logic              RES,
  input  logic              get,
  input  logic              put,
  input  logic              full,
  input  logic              empty,
  input  logic [WIDTH-1:0]  DIN,
  input  logic [WIDTH-1:0]  DOUT,
  input  logic [63:0]       head,
  input  logic              get_release,
  input  logic              put_release,
  input  logic              to_get,
  input  logic              to_put
);

  default clocking cb @(posedge GCLK); endclocking
  default disable iff (RES);

  // Reset brings system to known state (next cycle after RES=1 edge)
  assert property ($rose(RES) |=> head==0 && full==0 && empty==1 && get_release && put_release);

  // One-shot pulse behavior and gating
  assert property (to_get |-> get);
  assert property (to_put |-> put);
  assert property (get && !$past(get) |-> to_get);
  assert property (put && !$past(put) |-> to_put);
  assert property (get &&  $past(get) |-> !to_get);
  assert property (put &&  $past(put) |-> !to_put);

  // Release logic behavior
  assert property (!get |-> get_release);
  assert property (!put |-> put_release);
  assert property (to_get |=> !get_release);
  assert property (to_put |=> !put_release);

  // Combinational decode equivalence (sanity)
  assert property (to_get == (get && get_release));
  assert property (to_put == (put && put_release));

  // Pointer/flag invariants
  assert property (head <= LENGTH);
  assert property (!(full && empty));
  assert property (full  == (head == LENGTH));
  assert property (empty == (head == 0));

  // Legal operation constraints (prevent data loss/no-ops)
  assert property (to_put && !to_get |-> !full);
  assert property (to_get && !to_put |-> !empty);

  // Head/flag updates
  assert property (!full  && to_put && !to_get |=> head == $past(head)+1 && !empty);
  assert property (!empty && to_get && !to_put |=> head == $past(head)-1 && !full);
  assert property ($past(head)==LENGTH-1 && to_put && !to_get |=> full  && head==LENGTH);
  assert property ($past(head)==1         && to_get && !to_put |=> empty && head==0);
  assert property (to_get && to_put |=> head==$past(head) && full==$past(full) && empty==$past(empty));

  // Datapath checks
  // Simultaneous get+put passes DIN through to DOUT
  assert property (to_get && to_put |=> DOUT == $past(DIN));
  // From empty: single put then get returns that DIN
  assert property (empty && to_put && !to_get ##1 to_get && !to_put |=> DOUT == $past(DIN,2));

  // Coverage: fill, drain, simultaneous ops
  cover property (empty ##1 (to_put && !to_get)[*LENGTH] ##1 full);
  cover property (full  ##1 (to_get && !to_put)[*LENGTH] ##1 empty);
  cover property (to_get && to_put);
  cover property ($past(full)  && to_get && to_put);
  cover property ($past(empty) && to_get && to_put);

endmodule

// Bind into all queue instances; connects to internal signals as well.
bind queue queue_sva #(.WIDTH(WIDTH), .LENGTH(LENGTH)) queue_sva_i (
  .GCLK(GCLK),
  .RES(RES),
  .get(get),
  .put(put),
  .full(full),
  .empty(empty),
  .DIN(DIN),
  .DOUT(DOUT),
  .head(head),
  .get_release(get_release),
  .put_release(put_release),
  .to_get(to_get),
  .to_put(to_put)
);