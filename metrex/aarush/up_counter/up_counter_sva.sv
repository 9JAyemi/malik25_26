`timescale 1ns / 1ps

module tb_up_counter;

  // DUT signals
  logic clk;
  logic reset;
  logic select;
  wire [3:0] count_out;

  // Instantiate DUT
  up_counter dut (
    .clk(clk),
    .reset(reset),
    .select(select),
    .count_out(count_out)
  );

  // Clock generation
  always #5 clk = ~clk;

  // Stimulus
  initial begin
    clk = 0;
    reset = 1;
    select = 0;
    #10;
    reset = 0;

    // Normal counting mode
    repeat (5) @(posedge clk);
    
    // Complement select mode
    select = 1;
    repeat (5) @(posedge clk);

    // Reset again
    reset = 1;
    @(posedge clk);
    reset = 0;

    repeat (5) @(posedge clk);

    $finish;
  end

  // -------------------------------
  // SYSTEMVERILOG ASSERTIONS (SVA)
  // -------------------------------

  // 1️⃣ Reset clears both registers
  property reset_clears;
    @(posedge clk) reset |-> (dut.count_reg == 16'h0000 && dut.count_out == 4'h0);
  endproperty
  assert property (reset_clears)
    else $error("❌ Reset did not clear count_reg and count_out");

  // 2️⃣ Count increments by 1 each cycle when not reset
  property increment_behavior;
    @(posedge clk) disable iff (reset)
      dut.count_reg == $past(dut.count_reg + 1);
  endproperty
  assert property (increment_behavior)
    else $error("❌ count_reg did not increment correctly");

  // 3️⃣ When select = 0, output should match lower 4 bits of count_reg
  property select_zero_behavior;
    @(posedge clk) disable iff (reset)
      (!select) |-> (count_out == dut.count_reg[3:0]);
  endproperty
  assert property (select_zero_behavior)
    else $error("❌ count_out mismatch when select=0");

  // 4️⃣ When select = 1, output should be bitwise complement of count_reg[3:0]
  property select_one_behavior;
    @(posedge clk) disable iff (reset)
      (select) |-> (count_out == ~dut.count_reg[3:0]);
  endproperty
  assert property (select_one_behavior)
    else $error("❌ count_out mismatch when select=1");

  // 5️⃣ Overflow wrap-around check (for count_reg)
  property wrap_around_check;
    @(posedge clk) disable iff (reset)
      ($past(dut.count_reg) == 16'hFFFF) |-> (dut.count_reg == 16'h0000);
  endproperty
  assert property (wrap_around_check)
    else $error("❌ Counter did not wrap around after 0xFFFF");

endmodule
