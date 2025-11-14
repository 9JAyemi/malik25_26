// SVA for spi2. Bind this module to the DUT.
// Example: bind spi2 spi2_sva sva(.clock(clock), .sck(sck), .sdo(sdo), .sdi(sdi), .bsync(bsync), .start(start), .rdy(rdy), .speed(speed), .din(din), .dout(dout), .counter(counter), .enable_n(enable_n), .shiftin(shiftin), .shiftout(shiftout), .ena_shout_load(ena_shout_load), .g_ena(g_ena), .wcnt(wcnt));

module spi2_sva(
  input logic         clock,
  input logic         sck,
  input logic         sdo,
  input logic         sdi,
  input logic         bsync,
  input logic         start,
  input logic         rdy,
  input logic  [1:0]  speed,
  input logic  [7:0]  din,
  input logic  [7:0]  dout,

  // internal DUT signals (bind to hierarchical names in spi2)
  input logic  [4:0]  counter,
  input logic         enable_n,
  input logic  [6:0]  shiftin,
  input logic  [7:0]  shiftout,
  input logic         ena_shout_load,
  input logic         g_ena,
  input logic  [2:0]  wcnt
);
  default clocking cb @(posedge clock); endclocking
  wire busy = !enable_n;

  // Combinational equivalences
  assert property (rdy == enable_n);
  assert property (sck == counter[0]);
  assert property (enable_n == counter[4]);
  assert property (sdo == shiftout[7]);
  assert property (ena_shout_load == ((start || sck) && g_ena));
  assert property (g_ena ==
                   ((speed==2'b00) ? 1'b1 :
                    (speed==2'b01) ? (wcnt[0]  == 1'b0) :
                    (speed==2'b10) ? (wcnt[1:0]== 2'b00) :
                                     (wcnt[2:0]== 3'b000)));

  // wcnt behavior
  assert property (speed==2'b00 |-> wcnt==3'b000);
  assert property ((speed!=2'b00 && start)         |=> wcnt==3'b001);
  assert property ((speed!=2'b00 && !start && enable_n) |=> wcnt==3'b000);
  assert property ((speed!=2'b00 && !start && busy) |=> wcnt == $past(wcnt)+3'd1);

  // Counter behavior
  assert property (g_ena && start |=> counter==5'b00000);
  assert property (g_ena && !start && busy |=> counter == $past(counter) + 5'd1);
  assert property ((!g_ena || (g_ena && !start && !busy)) |=> $stable(counter));

  // SCK activity while busy (driven by counter[0])
  assert property (g_ena && !start && busy |=> sck != $past(sck));
  assert property (!busy |-> $stable(counter) && $stable(sck));

  // bsync behavior
  assert property (g_ena && start |=> bsync==1'b1);
  assert property (g_ena && !start && sck |=> bsync==1'b0);

  // shiftout load/rotate
  assert property (ena_shout_load && start  |=> shiftout == din);
  assert property (ena_shout_load && !start |=> shiftout == { $past(shiftout[6:0]), $past(shiftout[0]) });
  assert property (!ena_shout_load |=> $stable(shiftout));

  // shiftin sample on !sck; hold otherwise (under g_ena)
  assert property (g_ena && !sck |=> shiftin == { $past(shiftin[5:0]), $past(sdi) });
  assert property (g_ena && sck  |=> $stable(shiftin));

  // dout update only at last bit time; otherwise stable
  assert property (g_ena && !sck && (&counter[3:1]) && busy
                   |=> dout == { $past(shiftin[6:0]), $past(sdi) });
  assert property (!(g_ena && !sck && (&counter[3:1]) && busy) |=> $stable(dout));

  // When g_ena is low, state holds
  assert property (!g_ena |=> $stable({counter, bsync, shiftout, shiftin, dout}));

  // Start accepted implies not-ready next cycle
  assert property (g_ena && start |=> !rdy);

  // Liveness (transaction completes eventually)
  assert property (g_ena && start |-> ##[1:$] rdy);

  // Coverage
  cover property (g_ena && start ##[1:$] (rdy && $changed(dout)));
  cover property (speed==2'b00 && g_ena && start ##[1:$] rdy);
  cover property (speed==2'b01 && g_ena && start ##[1:$] rdy);
  cover property (speed==2'b10 && g_ena && start ##[1:$] rdy);
  cover property (speed==2'b11 && g_ena && start ##[1:$] rdy);
  cover property (ena_shout_load && !start ##1 $changed(shiftout));
  cover property (g_ena && !sck && (&counter[3:1]) && busy ##1 $changed(dout));
endmodule