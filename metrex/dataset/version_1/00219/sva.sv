// SVA checkers and binds for top_module and mux2to1

// Generic 2:1 mux checker (binds to every mux2to1)
module mux2to1_sva(
  input logic [3:0] a,
  input logic [3:0] b,
  input logic       sel,
  input logic [3:0] out
);
  // Functional correctness when select is known
  assert property (@(a or b or sel or out)
                   !$isunknown(sel) |-> (out === (sel ? b : a)))
    else $error("mux2to1: out mismatch (sel=%b a=%0h b=%0h out=%0h)", sel, a, b, out);

  // X-merge behavior: if inputs equal and select unknown, out must equal that value
  assert property (@(a or b or sel or out)
                   $isunknown(sel) && (a===b) |-> (out === a))
    else $error("mux2to1: out should equal inputs when a==b and sel is X/Z");

  // If inputs and select are all known, out must be known
  assert property (@(a or b or sel or out)
                   !$isunknown({a,b,sel}) |-> !$isunknown(out))
    else $error("mux2to1: X/Z on out with known inputs/sel");

  // Coverage: both selections and select edges
  cover property (@(a or b or sel) (sel==1'b0 && out===a));
  cover property (@(a or b or sel) (sel==1'b1 && out===b));
  cover property (@(negedge sel) 1);
  cover property (@(posedge sel) 1);
endmodule


// Top-level end-to-end 4:1 mux checker
module top_module_sva(
  input logic [3:0] a,
  input logic [3:0] b,
  input logic [3:0] c,
  input logic [3:0] d,
  input logic [1:0] sel,
  input logic [3:0] out_mux
);
  // End-to-end 4:1 mux mapping when both selects are known
  assert property (@(a or b or c or d or sel or out_mux)
                   !$isunknown(sel) |->
                     (out_mux === (sel==2'b00 ? a :
                                   sel==2'b01 ? b :
                                   sel==2'b10 ? c : d)))
    else $error("top_module: out_mux mismatch (sel=%b a=%0h b=%0h c=%0h d=%0h out=%0h)",
                sel, a, b, c, d, out_mux);

  // Coverage: observe all 4 selections and both select-bit edges
  cover property (@(a or b or c or d or sel or out_mux) (sel==2'b00 && out_mux===a));
  cover property (@(a or b or c or d or sel or out_mux) (sel==2'b01 && out_mux===b));
  cover property (@(a or b or c or d or sel or out_mux) (sel==2'b10 && out_mux===c));
  cover property (@(a or b or c or d or sel or out_mux) (sel==2'b11 && out_mux===d));

  cover property (@(posedge sel[0]) 1);
  cover property (@(negedge sel[0]) 1);
  cover property (@(posedge sel[1]) 1);
  cover property (@(negedge sel[1]) 1);
endmodule


// Bind the checkers
bind mux2to1  mux2to1_sva  u_mux2to1_sva(.a(a), .b(b), .sel(sel), .out(out));
bind top_module top_module_sva u_top_sva(.a(a), .b(b), .c(c), .d(d), .sel(sel), .out_mux(out_mux));