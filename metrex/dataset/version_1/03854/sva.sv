// SVA for counter. Bind this module to the DUT.
module counter_sva #(parameter WIDTH=8)
(
  input  logic                  clk,
  input  logic                  rst,
  input  logic                  load,
  input  logic [WIDTH-1:0]      data_in,
  input  logic [WIDTH-1:0]      count,
  input  logic                  max_count
);
  localparam logic [WIDTH-1:0] MAX = {WIDTH{1'b1}};
  localparam logic [WIDTH-1:0] ZERO = {WIDTH{1'b0}};

  // Asynchronous reset clears outputs immediately
  assert property (@(posedge rst) 1 |-> ##0 (count==ZERO && max_count==1'b0));

  // While reset is held, outputs remain zero on every clk
  assert property (@(posedge clk) rst |-> (count==ZERO && max_count==1'b0));

  // Load takes priority: next cycle reflect data_in, max_count low
  assert property (@(posedge clk) (!rst && load) |=> (count==data_in && max_count==1'b0));

  // Increment without wrap
  assert property (@(posedge clk) disable iff (rst)
                   (!load && $past(!rst) && $past(!load) && $past(count)!=MAX)
                   |-> (count==$past(count)+{{(WIDTH-1){1'b0}},1'b1} && max_count==1'b0));

  // Wrap when previous count was MAX (only when not loading)
  assert property (@(posedge clk) disable iff (rst)
                   (!load && $past(!rst) && $past(!load) && $past(count)==MAX)
                   |-> (count==ZERO && max_count==1'b1));

  // max_count only on wrap and coincides with count==0
  assert property (@(posedge clk) disable iff (rst)
                   max_count |-> (!load && count==ZERO && $past(!rst) && $past(!load) && $past(count)==MAX));

  // max_count is a single-cycle pulse
  assert property (@(posedge clk) disable iff (rst) max_count |=> !max_count);

  // No X/Z on observable outputs when not in reset
  assert property (@(posedge clk) disable iff (rst) !$isunknown({count, max_count}));

  // ---------------- Coverage ----------------

  // See a normal increment
  cover property (@(posedge clk) disable iff (rst)
                  (!load && $past(!load) && $past(count)!=MAX && count==$past(count)+1 && !max_count));

  // See a natural wrap (no load) at MAX
  cover property (@(posedge clk) disable iff (rst)
                  (!load && $past(!load) && $past(count)==MAX && max_count && count==ZERO));

  // Load any value (not MAX) and then increment next
  cover property (@(posedge clk) (!rst && load && data_in!=MAX)
                  ##1 (!load && count==$past(data_in)+1 && !max_count));

  // Load MAX and observe wrap on the following cycle
  cover property (@(posedge clk) (!rst && load && data_in==MAX)
                  ##1 (!load && max_count && count==ZERO));
endmodule

// Bind into the DUT
bind counter counter_sva #(.WIDTH(8)) counter_sva_i (
  .clk(clk),
  .rst(rst),
  .load(load),
  .data_in(data_in),
  .count(count),
  .max_count(max_count)
);