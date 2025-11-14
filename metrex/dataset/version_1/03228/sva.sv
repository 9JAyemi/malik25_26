// SVA for top_module
module top_module_sva (
  input  logic        clk,
  input  logic        reset,
  input  logic [7:0]  in1,
  input  logic [7:0]  in2,
  input  logic        select,
  input  logic [7:0]  out,
  input  logic [7:0]  sum,
  input  logic [7:0]  diff
);
  default clocking cb @(posedge clk); endclocking

  // Combinational arithmetic correctness of submodules
  assert property (sum  == ((in1 + in2) & 8'hFF));
  assert property (diff == ((in1 - in2) & 8'hFF));

  // Reset behavior (synchronous)
  assert property (reset |=> (out == 8'h00));

  // Registered datapath: out equals prior-cycle selected op when prior-cycle was not reset
  assert property ((!reset) |=> (out == $past(select ? ((in1 - in2) & 8'hFF)
                                                     : ((in1 + in2) & 8'hFF))));

  // No X after reset deasserts
  assert property ((!reset) |=> !$isunknown(out));

  // Stability when inputs and select are stable
  assert property ((!reset && $stable(in1) && $stable(in2) && $stable(select)) |=> $stable(out));

  // Coverage
  cover property ((!reset && !select) |=> (out == $past((in1 + in2) & 8'hFF)));
  cover property ((!reset &&  select) |=> (out == $past((in1 - in2) & 8'hFF)));
  cover property (!reset && ({1'b0,in1} + {1'b0,in2})[8]); // add overflow
  cover property (!reset && (in1 < in2));                  // sub borrow/underflow
  cover property (!reset && !select ##1 select);           // both ops seen
  cover property ($rose(reset) ##1 !reset);                // reset release
endmodule

bind top_module top_module_sva sva_i(
  .clk(clk),
  .reset(reset),
  .in1(in1),
  .in2(in2),
  .select(select),
  .out(out),
  .sum(sum),
  .diff(diff)
);