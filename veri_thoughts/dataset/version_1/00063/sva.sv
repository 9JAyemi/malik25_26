// SVA for binary_counter
module binary_counter_sva #(parameter WIDTH=16) (
  input  logic                clk,
  input  logic                rst,
  input  logic [WIDTH-1:0]    max_count,
  input  logic [WIDTH-1:0]    count,
  input  logic                done
);

  // Asynchronous reset: immediate and hold behavior
  assert property (@(posedge rst) (count=='0 && done==1'b0))
    else $error("Async reset did not drive count/done to 0 immediately");
  assert property (@(posedge clk) rst |-> (count=='0 && done==1'b0))
    else $error("While rst=1, count/done must hold at 0");

  // Next-state functional correctness (gated off reset entry)
  assert property (@(posedge clk) disable iff (rst)
                   !$past(rst) |-> count == ( ($past(count)==$past(max_count)) ? '0 : ($past(count)+1) ))
    else $error("count next-state mismatch");
  assert property (@(posedge clk) disable iff (rst)
                   !$past(rst) |-> done == ($past(count)==$past(max_count)))
    else $error("done must reflect prior equality of count==max_count");

  // When done is asserted, count must be 0 in the same cycle
  assert property (@(posedge clk) disable iff (rst) done |-> (count=='0))
    else $error("done asserted without count==0");

  // Basic X checks on outputs (outside of reset)
  assert property (@(posedge clk) disable iff (rst) !$isunknown({count,done}))
    else $error("X/Z detected on outputs");

  // Coverage
  // - Observe a normal increment step
  cover property (@(posedge clk) disable iff (rst)
                  !$past(rst) && ($past(count)!= $past(max_count)) && (count==$past(count)+1) && !done);
  // - Observe a wrap event (equality -> reset to 0 with done=1)
  cover property (@(posedge clk) disable iff (rst)
                  !$past(rst) && ($past(count)==$past(max_count)) && (count=='0) && done);
  // - Observe a done rising edge
  cover property (@(posedge clk) disable iff (rst) $rose(done));
  // - Corner: max_count==0 leading to consecutive done assertions
  cover property (@(posedge clk) disable iff (rst) (max_count=='0) ##1 done ##1 done);

endmodule

// Bind into DUT
bind binary_counter binary_counter_sva #(.WIDTH(16)) u_binary_counter_sva (
  .clk(clk),
  .rst(rst),
  .max_count(max_count),
  .count(count),
  .done(done)
);