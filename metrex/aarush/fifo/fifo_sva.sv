/*
 * SVA QUALITY EVALUATION
 * ======================
 * The FIFO assertions have race conditions and incomplete corner case coverage. Properties
 * `p_write_level` and `p_read_level` assume level increments/decrements by exactly 1, but
 * don't account for simultaneous read+write operations where level might stay constant or
 * change differently. Property `p_read_data_correct` uses `##1` delay but checks against
 * `$past(dut.rd_ptr)` which creates a timing mismatch - it should verify the data was
 * written at that location previously, not just that it matches current storage. The pointer
 * wrapping behavior is not verified - properties only check range [0:7] but don't assert
 * that ptr resets to 0 after reaching 7. Critical gaps: no empty/full condition checks
 * (attempting to read from empty or write to full FIFO), no verification of the 64-bit to
 * 16-bit data transformation beyond just the lower bits, and no ordering guarantees (FIFO
 * property: first-in-first-out sequence preservation). The storage array content persistence
 * is never verified - writes could be lost and assertions wouldn't catch it if pointers
 * happen to increment correctly.
 *
 * Most Significant Flaw: Missing assertions for simultaneous read/write operations and
 * empty/full boundary conditions, which are the most common sources of FIFO bugs in production.
 *
 * Final Score: 6/10 - Basic pointer and level mechanics are checked, but critical FIFO
 * correctness properties (ordering, boundary conditions, concurrent operations) are absent.
 */

/*
 * SECOND SVA QUALITY EVALUATION
 * =============================
 * The assertions are logically incomplete and contain correctness flaws. The properties for `p_write_level` and `p_read_level` are naive; they check for `level` incrementing or decrementing on `wr_en` or `rd_en` respectively, but completely fail to account for the critical case of simultaneous read and write, where the level should remain unchanged. The `p_read_data_correct` property is flawed, as it checks that `rd_data` matches the content of `storage` at the location pointed to by `$past(dut.rd_ptr)`, creating a potential race condition and failing to verify the fundamental FIFO data-ordering property.
 *
 * The verification coverage is critically insufficient for a FIFO. There are no assertions to check for illegal operations, such as writing when the FIFO is full or reading when it is empty. The pointer wrapping logic is not verified; the properties only check that the pointers stay within range but not that they correctly wrap from 7 to 0. Furthermore, the core First-In-First-Out behavior is not verified; a proper check would involve tracking a written data value and ensuring it is the one read out after all preceding data has been read.
 *
 * Most Significant Flaw: The complete absence of assertions for FIFO full/empty conditions and the failure to correctly model pointer/level behavior during simultaneous read/write operations.
 *
 * Final Score: 3/10 - The suite checks only the simplest, non-concurrent operations and misses all the critical boundary conditions that define a correct FIFO.
 */

`timescale 1ns/1ps

module tb_fifo;

  // DUT signals
  logic sys_clk;
  logic rst;
  logic wr_en;
  logic rd_en;
  logic [63:0] wr_data;
  logic [15:0] rd_data;
  logic can_burst;
  logic do_valid;

  // Instantiate DUT
  fifo dut (
    .sys_clk(sys_clk),
    .rst(rst),
    .wr_en(wr_en),
    .wr_data(wr_data),
    .rd_en(rd_en),
    .rd_data(rd_data),
    .can_burst(can_burst),
    .do_valid(do_valid)
  );

  // ==============================================================
  // Clock generation
  // ==============================================================
  always #5 sys_clk = ~sys_clk;

  // ==============================================================
  // Stimulus
  // ==============================================================
  initial begin
    sys_clk = 0;
    rst = 1;
    wr_en = 0;
    rd_en = 0;
    wr_data = 64'h0;
    #10;
    rst = 0;

    // Perform mixed write/read operations
    repeat (20) begin
      @(posedge sys_clk);
      wr_en = $urandom_range(0,1);
      rd_en = $urandom_range(0,1);
      wr_data = $random;
    end

    #20;
    $finish;
  end

  // ==============================================================
  // SYSTEMVERILOG ASSERTIONS
  // ==============================================================

  // 1. Reset behavior
  property p_reset_behavior;
    @(posedge sys_clk)
      rst |-> (dut.wr_ptr == 0 && dut.rd_ptr == 0 && dut.level == 0 &&
               can_burst == 0 && do_valid == 0);
  endproperty
  assert property (p_reset_behavior)
    else $error("Reset behavior failed!");

  // 2. Write operation correctness
  property p_write_pointer;
    @(posedge sys_clk)
      disable iff (rst)
      wr_en |-> ##1 (dut.wr_ptr == $past(dut.wr_ptr) + 1);
  endproperty
  assert property (p_write_pointer)
    else $error("Write pointer not incrementing correctly!");

  property p_write_level;
    @(posedge sys_clk)
      disable iff (rst)
      wr_en |-> ##1 (dut.level == $past(dut.level) + 1);
  endproperty
  assert property (p_write_level)
    else $error("FIFO level not incrementing on write!");

  // 3. Read operation correctness
  property p_read_pointer;
    @(posedge sys_clk)
      disable iff (rst)
      rd_en |-> ##1 (dut.rd_ptr == $past(dut.rd_ptr) + 1);
  endproperty
  assert property (p_read_pointer)
    else $error("Read pointer not incrementing correctly!");

  property p_read_level;
    @(posedge sys_clk)
      disable iff (rst)
      rd_en |-> ##1 (dut.level == $past(dut.level) - 1);
  endproperty
  assert property (p_read_level)
    else $error("FIFO level not decrementing on read!");

  // 4. do_valid correctness
  property p_do_valid_correct;
    @(posedge sys_clk)
      disable iff (rst)
      dut._do_valid == (dut.level > 0);
  endproperty
  assert property (p_do_valid_correct)
    else $error("_do_valid signal incorrect!");

  // 5. can_burst correctness
  property p_can_burst_correct;
    @(posedge sys_clk)
      disable iff (rst)
      dut._can_burst == ((dut.level + 4) <= 32);
  endproperty
  assert property (p_can_burst_correct)
    else $error("_can_burst signal incorrect!");

  // 6. Pointer range checks
  property p_pointer_range;
    @(posedge sys_clk)
      (dut.wr_ptr inside {[0:7]}) && (dut.rd_ptr inside {[0:7]});
  endproperty
  assert property (p_pointer_range)
    else $error("Pointer went out of range!");

  // 7. FIFO level range check
  property p_level_range;
    @(posedge sys_clk)
      (dut.level <= 32);
  endproperty
  assert property (p_level_range)
    else $error("FIFO level exceeded max depth!");

  // 8. Read data correctness (lower 16 bits match written word)
  property p_read_data_correct;
    @(posedge sys_clk)
      disable iff (rst)
      rd_en |-> ##1 (rd_data == $past(dut.storage[$past(dut.rd_ptr)])[15:0]);
  endproperty
  assert property (p_read_data_correct)
    else $error("Read data mismatch detected!");

  // 9. No X/Z outputs
  property p_no_xz_outputs;
    @(posedge sys_clk)
      !$isunknown({rd_data, can_burst, do_valid});
  endproperty
  assert property (p_no_xz_outputs)
    else $error("Unknown (X/Z) values found on outputs!");

endmodule
