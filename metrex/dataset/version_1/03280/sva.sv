// SVA for compare_data
// Bindable checker that asserts key behavior and provides concise coverage.

module compare_data_sva (
  input  logic        clk,
  input  logic        rst,
  input  logic [7:0]  data1,
  input  logic [7:0]  data2,
  input  logic [7:0]  data1_reg,
  input  logic [7:0]  data2_reg,
  input  logic [3:0]  byte_cnt,
  input  logic        eq,
  input  logic        done
);

  // Synchronous reset drives known state
  assert property (@(posedge clk)
    rst |-> (eq==0 && done==0 && byte_cnt==0 && data1_reg==0 && data2_reg==0)
  );

  // Byte counter legal range (0..7) and progression
  assert property (@(posedge clk) disable iff (rst)
    (byte_cnt <= 7)
  );

  assert property (@(posedge clk) disable iff (rst)
    $past(byte_cnt==0) |-> (byte_cnt==1)
  );

  assert property (@(posedge clk) disable iff (rst)
    $past(byte_cnt inside {[1:6]}) |-> (byte_cnt == $past(byte_cnt)+1)
  );

  assert property (@(posedge clk) disable iff (rst)
    $past(byte_cnt==7) |-> (byte_cnt==0)
  );

  // Input capture and data holding behavior
  assert property (@(posedge clk) disable iff (rst)
    $past(byte_cnt==0) |-> (data1_reg==$past(data1) && data2_reg==$past(data2))
  );

  assert property (@(posedge clk) disable iff (rst)
    $past(byte_cnt inside {[1:7]}) |-> (data1_reg==$past(data1_reg) && data2_reg==$past(data2_reg))
  );

  // Result and done at wrap
  assert property (@(posedge clk) disable iff (rst)
    $past(byte_cnt==7) |-> (done==1 && eq == ($past(data1_reg)==$past(data2_reg)) && byte_cnt==0)
  );

  // Control signal change points
  assert property (@(posedge clk)
    $rose(done) |-> $past(byte_cnt==7)
  );

  assert property (@(posedge clk)
    $fell(done) |-> rst
  );

  assert property (@(posedge clk) disable iff (rst)
    (eq != $past(eq)) |-> $past(byte_cnt==7)
  );

  assert property (@(posedge clk) disable iff (rst)
    ((data1_reg != $past(data1_reg)) || (data2_reg != $past(data2_reg))) |-> $past(byte_cnt==0)
  );

  // Minimal, meaningful coverage
  sequence s_full_count;
    (byte_cnt==0) ##1 (byte_cnt==1) ##1 (byte_cnt==2) ##1 (byte_cnt==3)
    ##1 (byte_cnt==4) ##1 (byte_cnt==5) ##1 (byte_cnt==6) ##1 (byte_cnt==7) ##1 (byte_cnt==0);
  endsequence

  cover property (@(posedge clk) disable iff (rst) s_full_count);
  cover property (@(posedge clk) $rose(done) && eq==1);
  cover property (@(posedge clk) $rose(done) && eq==0);

endmodule

// Bind into the DUT (tools allow connecting internals by name)
bind compare_data compare_data_sva sva_i (
  .clk(clk),
  .rst(rst),
  .data1(data1),
  .data2(data2),
  .data1_reg(data1_reg),
  .data2_reg(data2_reg),
  .byte_cnt(byte_cnt),
  .eq(eq),
  .done(done)
);