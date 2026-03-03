// SVA for hc161_like
// Bind these assertions to the DUT

module hc161_like_sva;

  // Access DUT signals directly via bind
  // Signals from hc161_like:
  //   input  [3:0] cpu_d;
  //   input        cpu_rw;
  //   input        Ncpu_romsel;
  //   reg   [3:0]  hc161_krn;
  //   output       hc161_out[3:0];

  default clocking cb @(posedge Ncpu_romsel); endclocking

  // Tracking flags
  logic past_valid, wrote_once;
  initial begin past_valid = 1'b0; wrote_once = 1'b0; end
  always_ff @(posedge Ncpu_romsel) begin
    past_valid <= 1'b1;
    if (!cpu_rw) wrote_once <= 1'b1;
  end

  // Structural: outputs mirror internal register (sampled on both edges)
  assert property (@(posedge Ncpu_romsel) {hc161_out3,hc161_out2,hc161_out1,hc161_out0} == hc161_krn);
  assert property (@(negedge Ncpu_romsel) {hc161_out3,hc161_out2,hc161_out1,hc161_out0} == hc161_krn);

  // Functional: write loads cpu_d at the same edge
  assert property (past_valid && !cpu_rw |-> hc161_krn == $past(cpu_d));

  // Functional: no-write (read) holds value
  assert property (past_valid &&  cpu_rw |-> hc161_krn == $past(hc161_krn));

  // Any change implies a write on that edge
  assert property (past_valid && (hc161_krn != $past(hc161_krn)) |-> !cpu_rw);

  // X-checks at capture
  assert property (!$isunknown(cpu_rw));
  assert property (!cpu_rw |-> !$isunknown(cpu_d));
  // After first write, outputs must be known
  assert property (wrote_once |-> !$isunknown({hc161_out3,hc161_out2,hc161_out1,hc161_out0}));

  // Coverage: observe write and read edges
  cover property (!cpu_rw);
  cover property ( cpu_rw);

  // Coverage: per-bit 0->1 and 1->0 transitions on writes
  genvar i;
  for (i = 0; i < 4; i++) begin : gen_bit_tog_cov
    cover property (past_valid && !cpu_rw && (hc161_krn[i] == 1'b1) && ($past(hc161_krn[i]) == 1'b0));
    cover property (past_valid && !cpu_rw && (hc161_krn[i] == 1'b0) && ($past(hc161_krn[i]) == 1'b1));
  end

  // Coverage: two consecutive writes with different data
  cover property (!cpu_rw ##1 (!cpu_rw && (hc161_krn != $past(hc161_krn,1))));

  // Coverage: all 16 values ever loaded
  covergroup cg_load @(posedge Ncpu_romsel);
    cp_val: coverpoint hc161_krn iff (!cpu_rw) { bins all_vals[] = {[0:15]}; }
  endgroup
  cg_load cg_load_i = new();

endmodule

bind hc161_like hc161_like_sva;