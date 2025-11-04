/*
 * SVA QUALITY EVALUATION
 * ======================
 * The assertions mix proper SVA properties with procedural checks in problematic ways. Property
 * `p_reset_clears_regs` uses `!$past(reset)` to detect reset deassertion, but the consequent checks
 * registers at the SAME cycle, not one cycle after, creating timing confusion - it should be `|=> `
 * (non-overlapping) not `|->` (overlapping). Property `p_pipeline_update` uses `$rose(clk)` redundantly
 * within `@(posedge clk)` and checks if registers equal `$past(next_*)` signals, but this creates a
 * sampling race: next_* are combinational and may change within the clock cycle. The combinational
 * assertion `next_alph == (al ^ ah)` is an immediate always @(*) check that could fire mid-evaluation
 * during simulation glitches. The decrypt_i check only validates one path but doesn't verify encrypt
 * mode correctness or the actual S-box lookup table values. Critical gaps: no verification of the
 * S-box substitution table correctness (are mappings cryptographically correct?), no inverse relationship
 * check between encrypt and decrypt operations (decrypt(encrypt(X)) should equal X), no verification of
 * multi-stage pipeline data flow, and the stability check using negedge is unreliable for catching
 * glitches in complex combinational paths.
 *
 * Most Significant Flaw: The S-box functional correctness is never verified - no assertions check
 * that the substitution table implements the correct cryptographic mapping or that encrypt/decrypt
 * are true inverses, making these assertions verify only timing, not functionality.
 *
 * Final Score: 5/10 - Pipeline timing checks are structurally present but have temporal operator
 * errors, and the complete absence of substitution table correctness verification means the core
 * cryptographic function remains unverified.
 */

/*
 * SECOND SVA QUALITY EVALUATION
 * =============================
 * The assertions exhibit a mix of poor SVA practices and logical errors. The reset property `p_reset_clears_regs` incorrectly uses an overlapping implication (`|->`) to check registers on the same cycle that reset is deasserted, which is temporally ambiguous. The pipeline update property `p_pipeline_update` is flawed; it compares registered values to the `$past` of combinational `next_*` signals, creating a race condition and failing to properly verify the synchronous transfer. The immediate assertion in the `always @(*)` block is susceptible to glitches and is not a robust way to check combinational logic.
 *
 * The verification is critically incomplete as it fails to validate the core cryptographic function of the S-box. There are no assertions to confirm that `data_o` is the correct substitution for `data_i` based on the S-box table for either encryption or decryption. The check for the decrypt path only confirms that `data_o` matches an internal signal (`inva`) but never verifies that `inva` itself is the correct inverse substitution. The crucial property that `decrypt(encrypt(x)) == x` is completely untested.
 *
 * Most Significant Flaw: The complete absence of any check to validate the functional correctness of the S-box lookup/substitution itself. The assertions verify pipeline timing but not whether the cryptographic transformation is correct.
 *
 * Final Score: 3/10 - The assertions contain temporal logic errors and, most importantly, fail to verify the fundamental cryptographic function of the S-box.
 */

`timescale 1ns/1ps

module sbox_sva();

  // signals for interfacing with DUT
  logic clk;
  logic reset;
  logic [7:0] data_i;
  logic decrypt_i;
  logic [7:0] data_o;

  // Instantiate DUT
  sbox dut (
    .clk(clk),
    .reset(reset),
    .data_i(data_i),
    .decrypt_i(decrypt_i),
    .data_o(data_o)
  );

  // simple clock
  initial clk = 0;
  always #5 clk = ~clk;

  // Reset check (active low): after reset is asserted, some internal regs are zero
  // Use $past to observe next-cycle behavior
  property p_reset_clears_regs;
    @(posedge clk) disable iff (0) !$past(reset) |-> (dut.to_invert == 4'b0000 && dut.ah_reg == 4'b0000 && dut.alph == 4'b0000);
  endproperty
  assert property (p_reset_clears_regs) else $error("Reset did not clear internal registers as expected");

  // Pipeline update property: on posedge clk the registers follow the next_* combinational signals
  property p_pipeline_update;
    @(posedge clk) disable iff (0) $rose(clk) |-> (dut.to_invert == $past(dut.next_to_invert) && dut.ah_reg == $past(dut.next_ah_reg) && dut.alph == $past(dut.next_alph));
  endproperty
  assert property (p_pipeline_update) else $error("Pipeline registers didn't update from next_* signals on clock edge");

  // Combinational relation: next_alph == al ^ ah
  always @(*) begin
    assert (dut.next_alph == (dut.al ^ dut.ah)) else $error("next_alph is not al ^ ah: al=%b ah=%b next_alph=%b", dut.al, dut.ah, dut.next_alph);
  end

  // When decrypt_i is 1 (decrypt path), final output should match inva through end_mux logic
  // Here we assert data_o == inva when decrypt_i != 0 (RTL's end_mux sets data_o=inva under default/decrypt mapping)
  always @(posedge clk) begin
    if (decrypt_i)
      assert (data_o == dut.inva) else $error("decrypt_i set but data_o != inva: data_o=%b inva=%b", data_o, dut.inva);
  end

  // Stability: data_o should not toggle inside the clock half-cycle
  logic [7:0] data_o_pos;
  always @(posedge clk) data_o_pos <= data_o;
  always @(negedge clk) begin
    assert (data_o == data_o_pos) else $error("data_o changed mid-cycle: posedge=%b negedge=%b", data_o_pos, data_o);
  end

  // small stimulus to exercise simulation assertions
  initial begin
    reset = 0; data_i = 8'h00; decrypt_i = 0; #20;
    reset = 1; #20;
    data_i = 8'h3C; decrypt_i = 0; #20;
    data_i = 8'hA5; decrypt_i = 1; #40;
    $finish;
  end

endmodule
