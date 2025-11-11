// SVA for wait_time_module
checker wait_time_checker(
  input logic        clk,
  input logic        reset,   // active-low
  input logic        work,
  input logic [11:0] wait_time,
  input logic [5:0]  i
);
  default clocking cb @ (posedge clk); endclocking

  // Asynchronous reset drives zeros
  assert property (@(posedge clk) !reset |-> (wait_time==12'd0 && i==6'd0));

  // All other checks disabled during reset
  default disable iff (!reset);

  // i is always within 0..4
  assert property (i <= 6'd4);

  // Hold when work==1
  assert property (work |=> $stable({wait_time,i}));

  // When work==0 and i<4: i increments, wait_time holds
  assert property ((!work && i < 6'd4) |=> (i == $past(i)+6'd1 && wait_time == $past(wait_time)));

  // When work==0 and i>=4: wait_time increments by 1 (with wrap), i resets to 0
  assert property ((!work && i >= 6'd4) |=> (i == 6'd0 &&
                   ((wait_time == $past(wait_time)+12'd1) ||
                    ($past(wait_time)==12'hFFF && wait_time==12'h000))));

  // Only allowed time wait_time changes is the increment point above
  assert property ((wait_time != $past(wait_time)) |->
                   ($past(!work && i >= 6'd4) &&
                    ((wait_time == $past(wait_time)+12'd1) ||
                     ($past(wait_time)==12'hFFF && wait_time==12'h000))));

  // Periodic stepping under continuous work==0 starting from i==0
  assert property ((!work && i==6'd0)
                   ##1 (!work && i==6'd1)
                   ##1 (!work && i==6'd2)
                   ##1 (!work && i==6'd3)
                   ##1 (!work && i==6'd4)
                   ##1 (!work && i==6'd0));

  // Coverage: one full increment cycle
  cover property ((!work && i==6'd0)
                  ##1 (!work && i==6'd1)
                  ##1 (!work && i==6'd2)
                  ##1 (!work && i==6'd3)
                  ##1 (!work && i==6'd4)
                  ##1 (!work && i==6'd0));

  // Coverage: wait_time wrap-around increment
  cover property (!work && i>=6'd4 && $past(wait_time)==12'hFFF
                  |=> (wait_time==12'h000 && i==6'd0));

  // Coverage: hold during work==1 for multiple cycles
  cover property (work[*3] ##1 !work);
endchecker

bind wait_time_module wait_time_checker u_wait_time_checker(
  .clk(clk), .reset(reset), .work(work), .wait_time(wait_time), .i(i)
);