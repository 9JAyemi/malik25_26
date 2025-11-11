// SVA for counter_rollover
// Concise, high-quality checks and coverage

// Bind these assertions to the DUT
bind counter_rollover counter_rollover_sva #(.W(W), .N(N)) u_counter_rollover_sva (.*);

module counter_rollover_sva
  #(parameter int W = 256,
    parameter int N = 4)
  (input  logic         CLK,
   input  logic         ENABLE,
   input  logic         LOAD,
   input  logic [W-1:0] DI,
   input  logic [W-1:0] DO,
   input  logic [N-1:0] ro,
   input  logic [N-1:0] tc);

  localparam int SLICE = (N>0) ? (W/N) : 0;

  // Static parameter checks
  initial begin
    if (W <= 0)            $fatal(1, "W must be > 0");
    if (N <= 0)            $fatal(1, "N must be > 0");
    if (W % N != 0)        $fatal(1, "W must be divisible by N");
    if (SLICE <= 0)        $fatal(1, "W/N must be > 0");
  end

  // Enable $past usage from 2nd cycle onward
  logic sample_en;
  initial sample_en = 1'b0;
  always @(posedge CLK) sample_en <= 1'b1;

  default clocking cb @(posedge CLK); endclocking

  // Golden next-state behavior
  // Priority: LOAD over ENABLE; ENABLE increments; else holds
  assert property (disable iff (!sample_en)
                   (LOAD && !$isunknown(DI)) |=> DO == DI);

  assert property (disable iff (!sample_en)
                   (!LOAD && ENABLE && !$isunknown($past(DO)))
                   |=> DO == $past(DO) + 1);

  assert property (disable iff (!sample_en)
                   (!LOAD && !ENABLE && !$isunknown($past(DO)))
                   |=> DO == $past(DO));

  // ro/tc chain correctness against DO bits
  genvar k;
  generate
    for (k = 0; k < N; k++) begin : gen_ro_tc_sva
      if (k == 0) begin
        assert property (disable iff (!sample_en)
                         !$isunknown(ENABLE) |-> ro[k] == ENABLE);
        assert property (disable iff (!sample_en)
                         tc[k] == 1'b1);
      end else begin : gen_kgt0
        localparam int HI = SLICE*k - 1;
        localparam int LO = 0;
        assert property (disable iff (!sample_en)
                         !$isunknown(DO[HI:LO]) |-> tc[k] == (&DO[HI:LO]));
        assert property (disable iff (!sample_en)
                         !$isunknown({ENABLE, DO[HI:LO]})
                         |-> ro[k] == (ENABLE && (&DO[HI:LO])));
      end
    end
  endgenerate

  // Key functional coverage
  cover property (disable iff (!sample_en)
                  (!LOAD && ENABLE));
  // Full-width rollover
  cover property (disable iff (!sample_en)
                  (!LOAD && ENABLE && !$isunknown($past(DO)) && $past(DO) == {W{1'b1}})
                  |=> DO == {W{1'b0}});
  // Load takes effect
  cover property (disable iff (!sample_en)
                  (LOAD && !$isunknown(DI)) |=> DO == DI);

endmodule