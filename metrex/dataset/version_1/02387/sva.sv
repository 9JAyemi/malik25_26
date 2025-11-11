Below is a concise, high-quality SVA bind module that fully checks the combinational behavior, X-handling, and independence from unused bits, plus essential coverage.

module AregInexactSlice_sva (
  input  logic        clk,
  input  logic [31:0] AM,
  input  logic        notAM31_3,
  input  logic        notAM2_0
);
  default clocking cb @(posedge clk); endclocking

  // Functional correctness (4-state aware)
  assert property (notAM31_3 === ~&AM[31:19]);
  assert property (notAM2_0  === ~&AM[2:0]);

  // Output must be known when its inputs are all known
  assert property (!$isunknown(AM[31:19]) |-> !$isunknown(notAM31_3));
  assert property (!$isunknown(AM[2:0])   |-> !$isunknown(notAM2_0));

  // Independence from unused AM[18:3] bits
  logic past_valid;
  initial past_valid = 1'b0;
  always_ff @(posedge clk) past_valid <= 1'b1;
  assert property (disable iff (!past_valid)
                   (AM[31:19] === $past(AM[31:19]) &&
                    AM[2:0]   === $past(AM[2:0])   &&
                    AM[18:3]  !== $past(AM[18:3]))
                   |-> (notAM31_3 === $past(notAM31_3) &&
                        notAM2_0  === $past(notAM2_0)));

  // Coverage: both output values and key corner cases
  cover property (notAM31_3 == 1'b0); // AM[31:19] all 1s
  cover property (notAM31_3 == 1'b1); // any 0 in AM[31:19]
  cover property (notAM2_0  == 1'b0); // AM[2:0] all 1s
  cover property (notAM2_0  == 1'b1); // any 0 in AM[2:0]
  cover property (AM[31:19] === {13{1'b1}} && notAM31_3 == 1'b0);
  cover property (AM[2:0]   === 3'b111      && notAM2_0  == 1'b0);
  cover property (notAM31_3 == 1'b0 && notAM2_0 == 1'b0);
  cover property (notAM31_3 == 1'b1 && notAM2_0 == 1'b1);
endmodule

// Example bind (provide a free-running clk from your TB or environment):
// bind AregInexactSlice AregInexactSlice_sva i_sva(.clk(tb_clk), .AM(AM), .notAM31_3(notAM31_3), .notAM2_0(notAM2_0));