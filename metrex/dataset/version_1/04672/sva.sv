// SVA checker for regfileparam_behav
// Focus: reset semantics, async read correctness via a tiny predictor, write effects, stability, X-checks, and key coverage.

`ifndef SYNTHESIS
module regfileparam_behav_sva
  #(parameter BITSIZE = 16,
    parameter ADDSIZE = 4)
(
  input  logic                   clk,
  input  logic                   rst,     // active-low
  input  logic                   wren,
  input  logic [ADDSIZE-1:0]     ra, rb, rw,
  input  logic [BITSIZE-1:0]     wdat,
  input  logic [BITSIZE-1:0]     adat, bdat, zeroDat
);

  localparam int DEPTH    = 1 << ADDSIZE;
  localparam int MAX_ADDR = DEPTH-1;

  // Lightweight reference model matching DUT semantics (async clear on negedge rst, write on posedge clk)
  logic [BITSIZE-1:0] model [0:DEPTH-1];

  always @(negedge rst or posedge clk) begin
    if (!rst) begin
      for (int i=0; i<DEPTH; i++) model[i] <= '0;
    end else if (wren) begin
      model[rw] <= wdat;
    end
  end

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst);

  // X-checks
  assert property (!$isunknown({rst,wren,ra,rb,rw})))
    else $error("Control signals contain X/Z");
  assert property (rst |-> !$isunknown({adat,bdat,zeroDat,wdat})))
    else $error("Data signals contain X/Z when out of reset");

  // Core functional checks
  // Outputs reflect model (covers async reads, zeroDat mirror)
  assert property (adat == model[ra]) else $error("adat mismatch");
  assert property (bdat == model[rb]) else $error("bdat mismatch");
  assert property (zeroDat == model[0]) else $error("zeroDat mismatch");

  // During reset, all reads are zero
  assert property (!rst |-> (adat=='0 && bdat=='0 && zeroDat=='0))
    else $error("Outputs not zero during reset");

  // Zero-address equivalence
  assert property ((ra==0) |-> (adat==zeroDat)) else $error("adat != zeroDat when ra==0");
  assert property ((rb==0) |-> (bdat==zeroDat)) else $error("bdat != zeroDat when rb==0");

  // Write visibility on next cycle for addressed port
  assert property (wren && (rw==ra) |=> adat == $past(wdat))
    else $error("Write to A address not observed next cycle");
  assert property (wren && (rw==rb) |=> bdat == $past(wdat))
    else $error("Write to B address not observed next cycle");

  // No-write-to-address implies read stability (address held)
  assert property ($stable(ra) && (!wren || (wren && rw!=ra)) |=> adat == $past(adat))
    else $error("adat changed without write to its address");
  assert property ($stable(rb) && (!wren || (wren && rw!=rb)) |=> bdat == $past(bdat))
    else $error("bdat changed without write to its address");

  // Coverage: key scenarios
  cover property (wren && (rw==0));                          // write to zero register
  cover property (wren && (rw==MAX_ADDR));                   // write to max address
  cover property (ra==rb);                                   // both read same address
  cover property (ra==0 && rb==0);                           // both read zero
  cover property (wren && (rw==ra));                         // write hits A
  cover property (wren && (rw==rb));                         // write hits B
  cover property (wren && (rw!=ra) && (rw!=rb));             // write to neither read port
  cover property ($rose(rst));                               // reset release

endmodule

// Bind into the DUT
bind regfileparam_behav regfileparam_behav_sva #(.BITSIZE(BITSIZE), .ADDSIZE(ADDSIZE)) u_regfileparam_behav_sva
(
  .clk     (clk),
  .rst     (rst),
  .wren    (wren),
  .ra      (ra),
  .rb      (rb),
  .rw      (rw),
  .wdat    (wdat),
  .adat    (adat),
  .bdat    (bdat),
  .zeroDat (zeroDat)
);
`endif