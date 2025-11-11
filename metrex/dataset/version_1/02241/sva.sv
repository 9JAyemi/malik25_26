// SVA for fmlarb_dack
// Bindable, concise, and checks key behaviors with coverage

module fmlarb_dack_sva (
  input  logic sys_clk,
  input  logic sys_rst,
  input  logic stb,
  input  logic eack,
  input  logic we,
  input  logic stbm,
  input  logic ack
);

  // Derived intents
  logic read, write;
  assign read  = eack & ~we;
  assign write = eack &  we;

  // Golden model for mask to check stbm
  logic emask;
  always_ff @(posedge sys_clk) begin
    if (sys_rst) emask <= 1'b0;
    else emask <= ack ? 1'b0 : (eack ? 1'b1 : emask);
  end

  // Past-valid tracker for 3-cycle history
  logic pv1, pv2, pv3;
  always_ff @(posedge sys_clk) begin
    if (sys_RST) begin pv1<=0; pv2<=0; pv3<=0; end
    else          begin pv1<=1; pv2<=pv1; pv3<=pv2; end
  end

  // Sanity/well-formedness
  assert property (@(posedge sys_clk) !(read && write));
  assert property (@(posedge sys_clk) eack |-> (read ^ write));
  assert property (@(posedge sys_clk) sys_rst |-> !ack);
  assert property (@(posedge sys_clk) !$isunknown({ack,stbm}));

  // ACK behavior
  assert property (@(posedge sys_clk) disable iff (sys_rst) write |-> ack);
  assert property (@(posedge sys_clk) disable iff (sys_rst) !pv3 |-> (ack == write));
  assert property (@(posedge sys_clk) disable iff (sys_rst) pv3 |-> (ack == (write || $past(read,3))));
  assert property (@(posedge sys_clk) disable iff (sys_rst) read |-> ##3 ack);

  // Mask/stbm behavior (via golden emask)
  assert property (@(posedge sys_clk) stbm == (stb && !emask));
  assert property (@(posedge sys_clk) disable iff (sys_rst) (eack && !ack) |=> emask);
  assert property (@(posedge sys_clk) disable iff (sys_rst) ack |=> !emask);

  // Functional coverage
  cover property (@(posedge sys_clk) disable iff (sys_rst) write && ack);                 // write immediate ACK
  cover property (@(posedge sys_clk) disable iff (sys_rst) read  ##3 ack);               // read 3-cycle ACK
  cover property (@(posedge sys_clk) disable iff (sys_rst) read ##1 read ##3 ack ##1 ack); // back-to-back reads -> back-to-back ACKs
  cover property (@(posedge sys_clk) disable iff (sys_rst)
                  (stb && read) ##1 (stb && !stbm) ##1 (stb && !stbm) ##1 (stb && stbm)); // stbm masking window for read
endmodule

bind fmlarb_dack fmlarb_dack_sva sva (
  .sys_clk(sys_clk),
  .sys_rst(sys_rst),
  .stb(stb),
  .eack(eack),
  .we(we),
  .stbm(stbm),
  .ack(ack)
);