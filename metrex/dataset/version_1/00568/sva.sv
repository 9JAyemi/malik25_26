// SVA for the given DUT. Bind these into the design.
// Focused, high-quality checks and concise coverage.

package top_sva_pkg;
  function automatic bit is_msb_idx8 (logic [7:0] n, logic [2:0] p);
    if (n==8'h00) return (p==3'd0);
    if (!n[p]) return 1'b0;
    for (int i=p+1; i<8; i++) if (n[i]) return 1'b0;
    return 1'b1;
  endfunction
endpackage


// Priority encoder checks
module priority_encoder_sva (
  input logic [7:0] in,
  input logic [2:0] out
);
  import top_sva_pkg::*;
  event ev; always @* -> ev; default clocking @(ev); endclocking

  assert property ((in==8'h00) |-> (out==3'd0))
    else $error("priority_encoder: out!=0 for in==0");

  assert property ((in!=8'h00) |-> is_msb_idx8(in,out))
    else $error("priority_encoder: out not MSB index of in");

  // Coverage: each MSB position and zero input
  genvar i;
  generate
    for (i=0;i<8;i++) begin : C_MSB
      cover property (in[i] && (i==7 ? 1'b1 : ~|in[7:i+1]));
    end
  endgenerate
  cover property (in==8'h00);
endmodule

bind priority_encoder priority_encoder_sva pe_sva (.in(in), .out(out));


// Adder/Subtractor checks
module adder_subtractor_sva (
  input logic [7:0] a, b, out,
  input logic       select
);
  event ev; always @* -> ev; default clocking @(ev); endclocking

  assert property (1 |-> out == (select ? (a - b) : (a + b)))
    else $error("adder_subtractor: out mismatch");

  // Coverage: both ops, plus wrap-around scenarios
  cover property (select==1'b0);
  cover property (select==1'b1);
  cover property (select==1'b0 && ((a + b) < a)); // add overflow (wrap)
  cover property (select==1'b1 && (a < b));       // sub underflow (wrap)
endmodule

bind adder_subtractor adder_subtractor_sva as_sva (.a(a), .b(b), .select(select), .out(out));


// Functional module checks
module functional_module_sva (
  input logic [2:0] pe_out,
  input logic [7:0] as_out,
  input logic [7:0] out
);
  event ev; always @* -> ev; default clocking @(ev); endclocking

  assert property ((as_out==8'h00) |-> (out==8'h00))
    else $error("functional_module: out must be 0 when as_out==0");

  assert property ((as_out!=8'h00) |-> (out[7:3]==5'b0 && out[2:0]==pe_out))
    else $error("functional_module: out must be zero-extended pe_out when as_out!=0");

  // Coverage: both gating paths; corner where pe_out==0 but as_out!=0
  cover property (as_out==8'h00);
  cover property (as_out!=8'h00);
  cover property (as_out!=8'h00 && pe_out==3'd0 && out==8'h00);
endmodule

bind functional_module functional_module_sva fm_sva (.pe_out(pe_out), .as_out(as_out), .out(out));


// Top-level integration check: priority encoder fed by (a+b)
module top_module_sva (
  input logic [7:0] a, b, sum, out,
  input logic       select,
  input logic [2:0] pos
);
  import top_sva_pkg::*;
  event ev; always @* -> ev; default clocking @(ev); endclocking

  assert property (is_msb_idx8(a + b, pos))
    else $error("top_module: pe.out must reflect MSB index of (a+b)");

  // Light integration coverage
  cover property ((a + b)==8'h00);
  cover property ((a + b)!=8'h00 && pos==3'd7);
endmodule

bind top_module top_module_sva top_sva (.a(a), .b(b), .select(select), .pos(pos), .sum(sum), .out(out));