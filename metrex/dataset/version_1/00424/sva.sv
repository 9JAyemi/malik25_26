// SVA for altera_tse_xcvr_resync
// Focus: end-to-end CDC intent, structural shift behavior, and minimal but strong coverage.
// Bind this module to the DUT instance.
`ifndef SYNTHESIS
module altera_tse_xcvr_resync_sva #(
  parameter SYNC_CHAIN_LENGTH = 2,
  parameter WIDTH             = 1,
  parameter SLOW_CLOCK        = 0
)(
  input  wire               clk,
  input  wire [WIDTH-1:0]   d,
  input  wire [WIDTH-1:0]   q
);
  localparam int INT_LEN = (SYNC_CHAIN_LENGTH > 0) ? SYNC_CHAIN_LENGTH : 1;

  default clocking cb @(posedge clk); endclocking

  // Warmup counter to ensure $past() history is valid
  localparam int HCW = (INT_LEN > 1) ? $clog2(INT_LEN+1) : 1;
  logic [HCW-1:0] hist_cnt;
  logic           hist_ready;
  always @(posedge clk) begin
    if (!hist_ready) hist_cnt <= hist_cnt + 1'b1;
  end
  assign hist_ready = (hist_cnt >= INT_LEN[HCW-1:0]);

  genvar gi;
  generate
    for (gi=0; gi<WIDTH; gi++) begin : gen_sva_per_bit

      // Structural shift-chain checks via hierarchical access
      // r is the synchronizer chain; q is last stage
      // Require a cycle of history to compare stages
      if (INT_LEN > 1) begin : gen_shift_checks
        genvar si;
        for (si=1; si<INT_LEN; si++) begin : gen_stage
          assert property (hist_ready |-> resync_chains[gi].r[si] == $past(resync_chains[gi].r[si-1]))
            else $error("Shift-chain stage mismatch bit %0d stage %0d", gi, si);
        end
      end
      assert property (resync_chains[gi].r[INT_LEN-1] === q[gi])
        else $error("q not tied to last stage of chain bit %0d", gi);

      // Fast path: Direct multi-flop resync
      if (SLOW_CLOCK == 0) begin : gen_fast
        assert property (hist_ready |-> q[gi] == $past(d[gi], INT_LEN))
          else $error("Pipeline latency mismatch (fast) bit %0d", gi);

        // Coverage: q follows d with INT_LEN latency (rise/fall)
        cover property (hist_ready && $rose(d[gi]) |-> ##INT_LEN $rose(q[gi]));
        cover property (hist_ready && $fell(d[gi]) |-> ##INT_LEN $fell(q[gi]));
      end

      // Slow path: input treated as a slow clock; pulse-stretch + resync
      else begin : gen_slow
        // If d is sampled high, synchronized q must go high within INT_LEN clk cycles
        assert property (hist_ready && d[gi] |-> ##[1:INT_LEN] q[gi])
          else $error("q did not assert after d high (slow) bit %0d", gi);

        // Once q is high while d is high, q must stay high until d goes low
        assert property ((q[gi] && d[gi]) |=> q[gi] until_with (!d[gi]))
          else $error("q deasserted while d still high (slow) bit %0d", gi);

        // After d falls while q is high, q must deassert within INT_LEN clk cycles
        assert property (q[gi] && $fell(d[gi]) |-> ##[1:INT_LEN] !q[gi])
          else $error("q did not clear after d fall (slow) bit %0d", gi);

        // q should not spuriously rise without a recent d high
        // Build "d was high in last INT_LEN samples" predicate
        logic d_high_recent;
        always @* begin
          d_high_recent = d[gi];
          for (int k=1; k<INT_LEN; k++) d_high_recent |= $past(d[gi], k, 1'b0);
        end
        assert property (hist_ready && $rose(q[gi]) |-> d_high_recent)
          else $error("Spurious q rise without recent d activity (slow) bit %0d", gi);

        // Coverage: d pulse -> q pulse -> clear
        cover property (hist_ready && $rose(d[gi])
                        ##[1:INT_LEN] $rose(q[gi])
                        ##[1:$]        $fell(d[gi])
                        ##[1:INT_LEN]  $fell(q[gi]));
      end

    end
  endgenerate
endmodule

// Bind SVA to all instances of the DUT
bind altera_tse_xcvr_resync
  altera_tse_xcvr_resync_sva #(
    .SYNC_CHAIN_LENGTH(SYNC_CHAIN_LENGTH),
    .WIDTH            (WIDTH),
    .SLOW_CLOCK       (SLOW_CLOCK)
  ) u_altera_tse_xcvr_resync_sva (.*);
`endif