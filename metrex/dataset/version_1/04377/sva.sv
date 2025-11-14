// SVA for descrambler
// Bindable, concise, full functional checks and essential coverage

`ifndef DESCRAMBLER_SVA_SV
`define DESCRAMBLER_SVA_SV

module descrambler_sva #(
  parameter int WIDTH = 512
)(
  input  logic                    clk,
  input  logic                    arst,
  input  logic                    ena,
  input  logic [WIDTH-1:0]        din,
  input  logic [WIDTH-1:0]        dout,
  input  logic [57:0]             scram_state,
  input  logic [WIDTH+58-1:0]     history
);

  localparam int S = 58;
  localparam int T = 19;

  // Parameter sanity
  initial begin
    assert (WIDTH >= S) else $error("descrambler WIDTH (%0d) must be >= %0d", WIDTH, S);
  end

  // Basic X checks
  assert property (@(posedge clk) !$isunknown(arst));
  assert property (@(posedge clk) disable iff (arst) !$isunknown({ena,din}));

  // history mapping
  assert property (@(posedge clk) history == {din, scram_state});

  // Asynchronous reset: immediate effect and hold while asserted
  assert property (@(posedge arst) ##0 (dout=='0 && scram_state=={S{1'b1}}));
  assert property (@(posedge clk) arst |-> (dout=='0 && scram_state=={S{1'b1}}));

  // Hold when disabled
  assert property (@(posedge clk) disable iff (arst)
                   !ena |=> (dout==$past(dout) && scram_state==$past(scram_state)));

  // scram_state update when enabled (captures upper 58 bits of din)
  assert property (@(posedge clk) disable iff (arst)
                   ena |=> (scram_state == $past(din[WIDTH-1 -: S])));

  // dout update when enabled: bit-accurate against XOR of history[i], history[i+19], history[i+58]
  genvar i;
  generate
    for (i=0; i<WIDTH; i++) begin : gen_dout_chk
      assert property (@(posedge clk) disable iff (arst)
                       ena |=> (dout[i] == ($past(history[i]) ^
                                            $past(history[i+T]) ^
                                            $past(history[i+S]))));
    end
  endgenerate

  // Minimal functional coverage
  cover property (@(posedge clk) arst ##1 !arst);
  cover property (@(posedge clk) disable iff (arst) $rose(ena));
  cover property (@(posedge clk) disable iff (arst) $fell(ena));
  cover property (@(posedge clk) disable iff (arst)
                  ena ##1 (scram_state == $past(din[WIDTH-1 -: S])));

endmodule

// Bind into DUT (accesses internal scram_state/history)
bind descrambler descrambler_sva #(.WIDTH(WIDTH)) u_descrambler_sva (
  .clk(clk),
  .arst(arst),
  .ena(ena),
  .din(din),
  .dout(dout),
  .scram_state(scram_state),
  .history(history)
);

`endif