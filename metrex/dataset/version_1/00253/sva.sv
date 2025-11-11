// SVA for wire_connection, anyedge, combined_system
// Quality-focused, concise checks and coverage

// ---------------- wire_connection ----------------
module wire_connection_sva (
  input a, b, c, select,
  input [7:0] x, y, out
);
  // react on any combinational change
  default clocking cb @(a or b or c or select or x or y or out); endclocking

  // Functional equivalence: out = (a ? (select ? x : y) : {8{c}})
  assert property (out === (a ? (select ? x : y) : {8{c}}));

  // b is functionally irrelevant
  assert property ($changed(b) && $stable({a,c,select,x,y}) |-> $stable(out));

  // Key path coverage
  cover property (a &&  select && out === x);
  cover property (a && !select && out === y);
  cover property (!a &&  c && out === {8{1'b1}});
  cover property (!a && !c && out === 8'h00);
endmodule

bind wire_connection wire_connection_sva
  (.a(a), .b(b), .c(c), .select(select), .x(x), .y(y), .out(out));


// ---------------- anyedge ----------------
module anyedge_sva (
  input clk,
  input [7:0] in, out
);
  default clocking cb @(posedge clk); endclocking

  // Rising-edge detector: out == in & ~past(in), ignore time 0
  assert property (disable iff ($initstate) out == (in & ~ $past(in)));

  // out only asserts where in is 1 this cycle
  assert property ((out & ~in) == '0);

  // No bit asserts on a falling or steady in-bit
  assert property (disable iff ($initstate) (in & $past(in)) == $past(in) |-> out == (in & ~ $past(in)));

  // Coverage: single-bit rise, all-bits rise, no-rise case
  cover property (disable iff ($initstate) ($rose(in[0]) && out[0]));
  cover property (disable iff ($initstate) ($past(in)==8'h00 && in==8'hFF && out==8'hFF));
  cover property (disable iff ($initstate) ($past(in)==in && out==8'h00));
endmodule

bind anyedge anyedge_sva
  (.clk(clk), .in(in), .out(out));


// ---------------- combined_system ----------------
module combined_system_sva (
  input clk, reset,
  input a, b, c, select,
  input [7:0] in,
  input [7:0] out,
  input [7:0] anyedge_out   // bind to internal wire
);
  default clocking cb @(posedge clk); endclocking

  // System-level simplification: out == anyedge_out & {8{a|c}}
  assert property (disable iff ($initstate) out == (anyedge_out & {8{a|c}}));

  // Cross-module equivalence using in-history
  assert property (disable iff ($initstate)
                   out == ((in & ~ $past(in)) & {8{a|c}}));

  // When a==1, select is irrelevant and out passes anyedge_out
  assert property (disable iff ($initstate) a |-> out == anyedge_out);

  // When a==0 and c==0, output is zero; when a==0 and c==1, pass anyedge_out
  assert property (disable iff ($initstate) (!a && !c) |-> out == 8'h00);
  assert property (disable iff ($initstate) (!a &&  c) |-> out == anyedge_out);

  // Out is always a subset of in
  assert property (disable iff ($initstate) (out & ~in) == '0);

  // b is functionally irrelevant to the system output
  assert property ($changed(b) && $stable({a,c,select,in}) |-> $stable(out));

  // Coverage: both gating modes and blocked mode
  cover property (disable iff ($initstate) a && out==anyedge_out);
  cover property (disable iff ($initstate) (!a && c) && out==anyedge_out);
  cover property (disable iff ($initstate) (!a && !c) && out==8'h00);
endmodule

bind combined_system combined_system_sva
  (.clk(clk), .reset(reset), .a(a), .b(b), .c(c), .select(select),
   .in(in), .out(out), .anyedge_out(anyedge_out));