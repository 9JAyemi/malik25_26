// SVA for spi_slave_simpler2
module spi_slave_simpler2_sva #(parameter int bc=8) (
  input logic              clk,
  input logic              cs,
  input logic              mosi,
  input logic              miso,
  input logic              sck,
  input logic              done,
  input logic [bc-1:0]     din,
  input logic [bc-1:0]     dout,
  input logic [bc-1:0]     shift_reg,
  input logic              prev_cs,
  input logic              prev_sck,
  input logic              mosi_sample,
  input logic [7:0]        shift_count
);
  default clocking cb @(posedge clk); endclocking
  bit past_valid; initial past_valid = 0; always_ff @(posedge clk) past_valid <= 1;
  default disable iff (!past_valid);

  // Combinational tie-offs
  assert property (miso == shift_reg[bc-1]);

  // History trackers
  assert property (prev_cs  == $past(cs));
  assert property (prev_sck == $past(sck));

  // CS behavior
  assert property (cs |-> done);
  assert property ($fell(cs) |-> (done==0 && shift_count==0));
  if (bc >= 8) begin : G_INIT8P
    assert property ($fell(cs) |-> (shift_reg[7:0]==8'h23));
    if (bc > 8) assert property ($fell(cs) |-> (shift_reg[bc-1:8]=='0));
  end else begin : G_INITLT8
    assert property ($fell(cs) |-> (shift_reg[bc-1:0]==8'h23[bc-1:0]));
  end
  // State holds when CS high
  assert property (cs |-> ($stable(shift_reg) && $stable(shift_count) && $stable(mosi_sample) && $stable(dout)));

  // SCK edge behavior under active CS
  assert property (!cs && $rose(sck) |-> (mosi_sample == mosi));
  assert property (!cs && $fell(sck) |-> (shift_count == $past(shift_count)+1));

  // Shift register updates only where expected
  assert property ((shift_reg != $past(shift_reg)) |-> ($fell(cs) || (!cs && $fell(sck))));
  if (bc >= 2) begin : G_SHIFTVAL
    assert property (!cs && $fell(sck) |-> (shift_reg == {$past(shift_reg[bc-2:0]), $past(mosi_sample)}));
  end

  // DONE and DOUT protocol
  assert property (!cs && $rose(sck) && (shift_count < bc-1) |-> !done);
  if (bc >= 2) begin : G_LASTRISE
    assert property (!cs && $rose(sck) && (shift_count==bc-1) |-> (done && (dout == {shift_reg[bc-2:0], mosi})));
  end else begin
    // bc==1: dout equals current mosi when the only bit is sampled
    assert property (!cs && $rose(sck) && (shift_count==bc-1) |-> (done && (dout[0] == mosi)));
  end
  assert property ((dout != $past(dout)) |-> (!cs && $rose(sck) && (shift_count==bc-1)));
  assert property ($fell(done) |-> $fell(cs));

  // Coverage
  cover property ($fell(cs) ##[1:$] (!cs && $rose(sck) && shift_count==bc-1 && done));
  cover property (!cs ##1 $rose(sck) ##1 $fell(sck));
endmodule

bind spi_slave_simpler2 spi_slave_simpler2_sva #(.bc(bc)) u_spi_slave_simpler2_sva (.*);