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
